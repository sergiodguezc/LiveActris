From dlfactris.lang Require Import metatheory.
From dlfactris.base_logic Require Export aprop.
From dlfactris.algebra Require Import multiset .
From dlfactris.base_logic Require Import cgraph.
From iris.bi.lib Require Import fixpoint_mono.
From dlfactris.bi.lib Require Import least_banach_fixpoint.
Import bi.

Definition inEdges := multiset aEdge.

Local Definition thread_inv_pre                                                  (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=148d1b60 *)
    (wp_prim : expr → (val → aProp) → aProp)
    (me : option expr) (ins : inEdges) : aProp :=
  match me with
  | None => ⌜⌜ ins = ∅ ⌝⌝
  | Some e => ⌜⌜ ins = ∅ ⌝⌝ ∗ wp_prim e (λ v, emp)%I
  end.

Definition heap_val_inv (hv : option heap_val) (ins : inEdges) : aProp :=
  match hv with
  | None => ⌜⌜ ins = ∅ ⌝⌝
  | Some (ChanHV None) =>
     ∃ Φ : val → aProp, ins ≡≡ {[+ inr (MiniProt ASend Φ); inr (MiniProt ARecv Φ) +]}
  | Some (ChanHV (Some v)) =>
     ∃ Φ : val → aProp, ins ≡≡ {[+ inr (MiniProt ARecv Φ) +]} ∗ Φ v
  | Some (RefHV v) => ins ≡≡ {[+ inl v +]}
  end.
Global Instance: Params (@heap_val_inv) 1 := {}.

Definition ginv (f : obj → inEdges → outEdges → siProp) : siProp :=              (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=599d07fc *)
  ∃ g : cgraph obj aEdge,
    ⌜ cgraph_wf g ⌝ ∧ ∀ ν, f ν (in_labels g ν) (out_edges g ν).

Definition reducible_or_blocked_own (e : expr) (h : heap) (Σ : outEdges) :=
  reducible e h ∨ ∃ l Φ, blocked e l h ∧ Σ !! Chan l = Some (inr (MiniProt ARecv Φ)).

Global Instance reducible_or_blocked_own_impl_ne e h n :
  Proper (dist n ==> impl) (reducible_or_blocked_own e h).
Proof.
  intros Σ1 Σ2 HΣ. rewrite /reducible_or_blocked_own. do 3 f_equiv.
  specialize (HΣ (Chan a)). revert HΣ.
  case _ : (Σ1 !! _)=> [hv1|]; case _ : (Σ2 !! _)=> [hv2|]; try by inversion 1.
  intros ?%(inj Some) (Φ & ? & ?); simplify_eq/=.
  destruct hv2 as [|[??]]; first by inv HΣ.
  apply (inj inr) in HΣ as [??]; simplify_eq/=; eauto.
Qed.
Global Instance reducible_or_blocked_own_ne e h n :
  Proper (dist n ==> iff) (reducible_or_blocked_own e h).
Proof. intros Σ1 Σ2 HΣ; split; by eapply reducible_or_blocked_own_impl_ne. Qed.

Local Definition inv'_pre (wp_prim : expr → (val → aProp) → aProp)               (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=01cdf805 *)
                          (σ : cfg) (tid : nat) (Σtid : outEdges) : siProp :=
  ginv (λ ν ins Σ,
    match ν with
    | Thread i =>
        if decide (tid = i) then
          ⌜ ins = ∅ ∧ tid < length σ.1 ⌝ ∧ Σtid ≡ Σ
        else
          aProp_at (thread_inv_pre wp_prim (σ.1 !! i) ins) Σ
    | Chan l => aProp_at (heap_val_inv (σ.2 !! l) ins) Σ
    end%I).

(* prim_step contains a flag b that says if the step was pure or not *)
Definition wp_prim_pre (wp_prim1 wp_prim2 : expr * (val -d> aProp) -d> aProp) :          (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a668d5e6 *)
    expr * (val -d> aProp) -d> aProp := λ '(e, Φ),
  match to_val e with
  | Some v => ◇ Φ v
  | None => AProp $ λ Σ,
     ∀ tid es h,
       ▷ inv'_pre (curry wp_prim1) (es, h) tid Σ →
         ◇ (⌜ reducible_or_blocked_own e h Σ ⌝ ∧
             ∀ e' h' es_new b,
               ⌜ prim_step e h e' h' es_new b ⌝ → ∃ Σtid , 
                 ▷ inv'_pre (curry wp_prim2) (es ++ es_new,h') tid Σtid ∧
                 ▷?(b) aProp_at (wp_prim2 (e', Φ)) Σtid) 
  end%I.

Global Instance heap_val_inv_ne cv : NonExpansive (heap_val_inv cv).
Proof.
  solve_proper_prepare. do 2 f_equiv; [by repeat f_equiv..|].
  rewrite -!multiset_empty_equiv_eq -!discrete_eq. by repeat f_equiv.
Qed.
Global Instance ginv_ne n :
  Proper
    (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n))) ==>
    dist n) ginv.
Proof. intros f f' Hf. rewrite /ginv. repeat f_equiv. apply Hf. Qed.

Local Instance thread_inv_pre_ne n :
  Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==>
          (=) ==> dist n ==> dist n) thread_inv_pre.
Proof.
  solve_proper_prepare.
  f_equiv; rewrite -!multiset_empty_equiv_eq -!discrete_eq; by repeat f_equiv.
Qed.

Local Instance inv'_pre_ne n :
  Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==>
          (=) ==> (=) ==> dist n ==> dist n) inv'_pre.
Proof. solve_proper. Qed.

Local Instance wp_prim_pre_mono (Φ : prodO exprO (val -d> aProp) -n> aProp) : BiMonoPred (wp_prim_pre Φ).
Proof.
   constructor.
   - iIntros (φ1 φ2 Hφ1 Hφ2).
     apply aProp_entails; iIntros (Σ ->).
     rewrite aProp_at_wand. iIntros (Σ _).
     rewrite aProp_at_intuitionistically left_id_L. iIntros "[-> HΦ]".
     clear Σ.
     rewrite !aProp_at_forall. iIntros ([e Ψ]) "/=".
     rewrite aProp_at_wand. iIntros (Σ _). rewrite (left_id_L ∅).
     destruct (to_val e); simpl; [by eauto|].
     iIntros "(%Σ' & HΣ & H)". iExists Σ'; iSplit; [done|].
     iIntros (tid es h) "Hinv".
     iMod ("H" with "Hinv") as "[Hred H]". iModIntro.
     iSplit; first by eauto.
     iIntros (e' h' es_new b Hps).
     iDestruct ("H" with "[]") as (Σtid) "[H1 H2]"; first done.
     iExists Σtid. iSplit.
     {
       iModIntro. iDestruct "H1" as (g Hwf) "H1".
       iExists g. iSplit; first done.
       iIntros (ν). iSpecialize ("H1" $! ν).
       destruct ν ; last done.
       destruct (decide (tid = n)) ; [done | simplify_eq/=].
       rewrite /thread_inv_pre.
       destruct ((es ++ es_new) !! n); last done.
       rewrite !aProp_at_sep_affinely_l. 
       iDestruct "H1" as "[? H1]"; iFrame.
       unfold curry.
       iSpecialize ("HΦ" $! (e0, λ _ : val, emp)%I).
       rewrite aProp_at_wand.
       replace (out_edges g (Thread n)) with (∅ ∪ (out_edges g (Thread n))) at 2 ; last first.
       { rewrite left_id_L //. }
       iApply "HΦ"; last done.
       iPureIntro. apply map_disjoint_empty_l.
     }
     iModIntro.
     iSpecialize ("HΦ" $! (e', Ψ)).
     rewrite aProp_at_wand.
     assert (∅ ##ₘ Σtid) as H3 by apply map_disjoint_empty_l.
     iSpecialize ("HΦ" $! Σtid H3).
     rewrite map_union_comm ; [|done].
     rewrite map_union_empty.
     by iApply "HΦ".
   - intros φ Hφ n [e1 Ψ] [e2 Ψ2] [H1 H2]. simpl in H1, H2.
     rewrite -H1 /wp_prim_pre.
     destruct (to_val e1) as [v1|] eqn:He1 ; simpl.
     + f_equiv; apply H2.
     + do 28 (f_contractive || f_equiv || done ) .
Qed.

Local Instance wp_prim_pre_ctr n : Proper (dist_later n ==> dist n ==> dist n) wp_prim_pre.
Proof.
  intros Φ1 Φ2 HΦ φ1 φ2 Hφ [x φ].
  rewrite /wp_prim_pre.
  destruct (to_val x); [done|].
  do 12 (f_contractive || f_equiv).
  - solve_proper_prepare.
    apply HΦ.
  - do 14 (f_contractive || f_equiv || done).
    solve_proper_prepare.
    specialize (Hφ (a8, a9)).
    apply (dist_le n) ; [done | lia ].
Qed.

Local Definition wp_prim_def := curry (least_banach_fixpoint wp_prim_pre).

Local Definition wp_prim_aux : seal (@wp_prim_def). Proof. by eexists. Qed.
Definition wp_prim : expr → (val → aProp) → aProp := wp_prim_aux.(unseal).
Local Definition wp_prim_unseal : wp_prim = _ := wp_prim_aux.(seal_eq).
Global Instance: Params (@wp_prim) 1 := {}.

Definition thread_inv := thread_inv_pre wp_prim.
Global Instance: Params (@thread_inv) 1 := {}.
Definition inv' := inv'_pre wp_prim.
Global Instance: Params (@inv') 2 := {}.

Lemma wp_prim_unfold e Φ :
  wp_prim e Φ ⊣⊢
    match to_val e with
    | Some v => ◇ Φ v
    | None => AProp $ λ Σ,
       ∀ tid es h,
         ▷ inv' (es,h) tid Σ →
         ◇ (⌜ reducible_or_blocked_own e h Σ ⌝ ∧
             ∀ e' h' es_new b,
               ⌜ prim_step e h e' h' es_new b ⌝ → ∃ Σtid , 
                 ▷ inv' (es ++ es_new,h') tid Σtid ∧
                 ▷?(b) aProp_at (wp_prim e' Φ) Σtid) 
    end.
Proof.
  rewrite /inv' wp_prim_unseal /wp_prim_def.
  replace (curry (least_banach_fixpoint wp_prim_pre) e Φ) with (least_banach_fixpoint wp_prim_pre (e, Φ)) by done.
  rewrite (least_banach_fixpoint_unfold _) //. 
Qed.

Lemma thread_inv_unfold me ins :
  thread_inv me ins ⊣⊢
    match me with
    | None => ⌜⌜ ins = ∅ ⌝⌝
    | Some e => ⌜⌜ ins = ∅ ⌝⌝ ∗ wp_prim e (λ v, emp)%I
    end.
Proof. done. Qed.

Lemma inv'_unfold tid Σtid σ :
  inv' σ tid Σtid ⊣⊢
    ginv (λ ν ins Σ,
      match ν with
      | Thread i =>
          if decide (tid = i) then
            ⌜ ins = ∅ ∧ tid < length σ.1 ⌝ ∧ Σtid ≡ Σ
          else
            aProp_at (thread_inv (σ.1 !! i) ins) Σ
      | Chan l => aProp_at (heap_val_inv (σ.2 !! l) ins) Σ
      end%I).
Proof. done. Qed.

Global Instance thread_inv_ne me : NonExpansive (thread_inv me).
Proof. solve_proper. Qed.
Global Instance thread_inv_proper me : Proper ((≡) ==> (≡)) (thread_inv me).
Proof. apply: ne_proper. Qed.

Global Instance inv'_ne σ tid : NonExpansive (inv' σ tid).
Proof. solve_proper. Qed.
Global Instance inv'_proper σ tid : Proper ((≡) ==> (≡)) (inv' σ tid).
Proof. apply: ne_proper. Qed.

(* Note: Now the proof is not using the well_foundedness of the definition *)
Global Instance wp_prim_ne e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp_prim e).
Proof.
  induction e ; rewrite wp_prim_unseal /wp_prim_def .
  all: solve_proper_prepare ;
       apply least_banach_fixpoint_ne ;
       split ; [done| apply H].
Qed.
Global Instance wp_prim_proper e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp_prim e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_prim_ne=> v; apply equiv_dist.
Qed.

Global Instance wp_prim_except_0 e Φ : IsExcept0 (wp_prim e Φ).
Proof.
  apply aProp_entails=> Σ. rewrite /bi_except_0. iIntros "[H|$]".
  rewrite aProp_at_later aProp_at_pure.
  rewrite wp_prim_unfold. destruct (to_val e).
  - rewrite aProp_at_except_0. by iMod "H".
  - iExists (Σ). iSplit; [done|]. by iMod "H".
Qed.

Lemma inv'_tid_irrelevant tid Σ e es h :
  inv' (es, h) tid Σ ⊢ inv' (<[tid:=e]> es, h) tid Σ.
Proof.
  rewrite !inv'_unfold.
  iDestruct 1 as (g ?) "Hinv". iExists g; iSplit; first done.
  iIntros (ν). iSpecialize ("Hinv" $! ν).
  destruct ν; [destruct (decide _) as [->|]|]; simpl;
    rewrite ?length_insert // list_lookup_insert_ne //.
Qed.

Lemma wp_prim_val Φ v : Φ v -∗ wp_prim (Val v) Φ.
Proof. rewrite wp_prim_unfold /=. eauto. Qed.

Lemma wp_prim_val_inv Φ v : wp_prim (Val v) Φ -∗ ◇ Φ v.
Proof. rewrite wp_prim_unfold /=. auto. Qed.

Definition wp_ind' (Ψ : prodO expr (val -d> aProp) -n> aProp) := least_banach_fixpoint_ind.

Local Definition Ind_wp_def (Ψ : expr → (val -d> aProp) → aProp)
  : expr → (val -d> aProp) → aProp := λ e Φ,
  wp_prim_pre (uncurry wp_prim) (λ '(e1, Φ1), (Ψ e1 Φ1 ∧ wp_prim e1 Φ1)%I) (e, Φ).

Local Definition Ind_wp_aux : seal (@Ind_wp_def). Proof. by eexists. Qed.
Definition Ind_wp : (expr → (val -d> aProp) → aProp) → expr → (val → aProp) → aProp := Ind_wp_aux.(unseal).
Local Definition Ind_wp_unseal : Ind_wp = _ := Ind_wp_aux.(seal_eq).
Global Instance: Params (@Ind_wp) 1 := {}.

Definition inv'_ind (Ψ : expr → (val -d> aProp) → aProp)
  := inv'_pre (λ e1 Φ1, (Ψ e1 Φ1 ∧ wp_prim e1 Φ1)%I).

Lemma inv'_ind_inv' Ψ σ tid Σtid :
  inv'_ind Ψ σ tid Σtid ⊢ inv' σ tid Σtid.
Proof.
  iIntros "H". rewrite !inv'_unfold /inv'_ind.
  iDestruct "H" as (g Hwf) "H". iExists g; iSplit; first done.
  iIntros (ν). iSpecialize ("H" $! ν).
  destruct ν ; last done.
  destruct (decide (tid = n)) ; [done | simplify_eq/=].
  rewrite /thread_inv /thread_inv_pre .
  destruct ((σ.1) !! n); last done.
  rewrite !aProp_at_sep_affinely_l.
  iDestruct "H" as "[? H]"; iFrame.
  rewrite aProp_at_and.
  iDestruct "H" as "[? H]"; iFrame.
Qed.

Lemma Ind_wp_unfold Ψ e Φ :
  Ind_wp Ψ e Φ ⊣⊢
    match to_val e with
    | Some v => ◇ Φ v
    | None => AProp $ λ Σ,
       ∀ tid es h,
         ▷ inv' (es,h) tid Σ →
         ◇ (⌜ reducible_or_blocked_own e h Σ ⌝ ∧
             ∀ e' h' es_new b,
               ⌜ prim_step e h e' h' es_new b ⌝ → ∃ Σtid , 
                 ▷ inv'_ind Ψ (es ++ es_new,h') tid Σtid ∧
                 ▷?(b) aProp_at (Ψ e' Φ ∧ wp_prim e' Φ) Σtid)
    end%I.
Proof.
  rewrite Ind_wp_unseal /Ind_wp_def.
  rewrite /wp_prim_pre curry_uncurry //.
Qed.

Lemma wp_prim_ind (Ψ : expr → (val -d> aProp) -n> aProp) :
    □ (∀ e1 Φ1 , Ind_wp Ψ e1 Φ1 -∗ Ψ e1 Φ1) ⊢ ∀ e Φ, wp_prim e Φ -∗ Ψ e Φ.
Proof.
  iIntros "IH" (e Φ) "Hwp".
  unshelve epose (Ψ1 := {| ofe_mor_car := uncurry Ψ ; ofe_mor_ne := _ |}).
  { intros n [e1 Φ1] [e2 Φ2] H; apply uncurry_ne; [|done]; solve_proper. }
  replace (Ψ e Φ) with (Ψ1 (e, Φ)) by done.
  replace (wp_prim e Φ) with (uncurry wp_prim (e, Φ)) by done.
  rewrite wp_prim_unseal /wp_prim_def uncurry_curry.
  iApply (least_banach_fixpoint_ind Ψ1 with "[IH]") ; last done.
  iApply intuitionistically_intro' ; [| iApply "IH"].
  iIntros "IH" ([e1 Φ1]) "HΨ".
  iApply "IH".
  rewrite Ind_wp_unfold /=.
  destruct (to_val e1) as [v1|] eqn:Heq ; [done|].
  iApply AProp_mono; last done.
  iIntros (Σ). simpl.
  rewrite /inv' wp_prim_unseal /wp_prim_def.
  iIntros "IH" (tid es h) "#Hinv". 
  - iDestruct ("IH" with "Hinv") as "[Hred IH]".
    iSplit ; first by iAssumption.
    iMod "IH". iIntros "!>" (e' h' es_new b ) "Hstep".
    iDestruct ("IH" with "[Hstep]") as (Σtid) "[H1 H2]"; first done.
    iExists Σtid. iSplit; last done. iModIntro.
    rewrite /inv'_ind /inv'_pre.
    iDestruct "H1" as (g Hwf) "H1".
    iExists g. iSplit; first done.
    iIntros (ν). iSpecialize ("H1" $! ν).
    destruct ν; last done.
    destruct (decide (tid = n)) ; first done.
    rewrite /thread_inv_pre /=.
    destruct ((es ++ es_new) !! n); last done.
    rewrite !aProp_at_sep_affinely_l.
    iDestruct "H1" as "[? H1]"; iFrame.
    unfold curry, uncurry.
    rewrite !aProp_at_and. 
    iDestruct "H1" as "[? H1]"; iFrame.
    rewrite wp_prim_unseal /wp_prim_def /curry //.
Qed.

Lemma wp_prim_ind_at (Ψ : expr → (val -d> aProp) -n> aProp) :
    (∀ e1 Φ1 Σ1, aProp_at (Ind_wp Ψ e1 Φ1) Σ1 → aProp_at (Ψ e1 Φ1) Σ1 ) ⊢
    ∀ e Φ Σ, aProp_at (wp_prim e Φ) Σ → aProp_at (Ψ e Φ) Σ.
Proof.
  iAssert (∀ Σ, aProp_at (□ (∀ e1 Φ1 , Ind_wp Ψ e1 Φ1 -∗ Ψ e1 Φ1)) Σ → ∀ e Φ Σ', ⌜ Σ ##ₘ Σ' ⌝ → aProp_at (wp_prim e Φ) Σ' → aProp_at (Ψ e Φ) (Σ ∪ Σ'))%I as "H".
  { pose (wp_prim_ind Ψ) as H.
    iIntros (Σ) "#IH".
    rewrite H.
    iIntros (e Φ). rewrite -(aProp_at_wand Σ).
    by iSpecialize ("IH" $! e Φ). }
  iAssert (aProp_at ((∀ e1 Φ1 , Ind_wp Ψ e1 Φ1 -∗ Ψ e1 Φ1)) ∅ → ∀ e Φ Σ, aProp_at (wp_prim e Φ) Σ → aProp_at (Ψ e Φ) Σ)%I as "H1".
  { iIntros "#IH".
    iIntros (e Φ Σ) "Hwp".
    replace (Σ) with (∅ ∪ Σ) at 2 by rewrite left_id_L //.
    iApply "H" ; try done.
    - rewrite aProp_at_intuitionistically. by iSplit.
    - iPureIntro. apply map_disjoint_empty_l.
  }
  iIntros "#IH". 
  iApply "H1".
  rewrite aProp_at_forall; iIntros (e).
  rewrite aProp_at_forall; iIntros (Φ).
  rewrite aProp_at_wand.
  iIntros (Σ1 ?).
  rewrite left_id_L.
  iApply "IH".
Qed.

Local Program Definition Ψmono : expr → (val -d> aProp) -n> aProp :=
  λ e, (λne (Φ2 : val -d> aProp),  (∀ Φ3, □ (∀ v, Φ2 v -∗ Φ3 v) -∗ wp_prim e Φ3)%I).
Next Obligation. solve_proper. Qed.

Lemma wp_prim_mono_aux e Φ1 : wp_prim e Φ1 -∗ ∀ Φ2, □(∀ v, Φ1 v -∗ Φ2 v) -∗ wp_prim e Φ2.
Proof.
  replace (∀ Φ2 : val → aPropI, □(∀ v : val, Φ1 v -∗ Φ2 v) -∗ wp_prim e Φ2)%I with (Ψmono e Φ1) by done.
  revert e Φ1.
  iApply wp_prim_ind.
  iIntros "!>" (e1 Φ1) "HInd".
  rewrite Ind_wp_unfold /Ψmono /=.
  iIntros (Φ2) "Hv".
  rewrite wp_prim_unfold.
  destruct (to_val e1) as [v1|] eqn:Heq.
  - iMod "HInd"; iModIntro; by iApply "Hv".
  - iApply AProp_mono; [|iApply AProp_sep_persistent; iFrame].
    iIntros (Σ) "[IH Hv] /=".
    iIntros (tid es h) "Hinv".
    iMod ("IH" with "Hinv") as "[Hred H]". iModIntro.
    iSplit; first done.
    iIntros (e' h' es_new b Hps).
    iDestruct ("H" with "[]") as (Σtid) "[H1 H2]"; first done.
    iExists Σtid. iSplit.
    { iNext; by iApply inv'_ind_inv'. }
    iModIntro.
    rewrite aProp_at_and.
    iDestruct "H2" as "[H2 H3]".
    rewrite !aProp_at_forall.
    iSpecialize ("H2" $! Φ2).
    rewrite aProp_at_wand.
    iSpecialize ("H2" $! ∅).
    iAssert (⌜Σtid ##ₘ ∅ ⌝)%I as "Hdisj".
    { iPureIntro. apply map_disjoint_empty_r. }
    iSpecialize ("H2" with "Hdisj").
    rewrite map_union_empty.
    iApply "H2".
    rewrite !aProp_at_intuitionistically.
    iSplit ; first done.
    rewrite aProp_at_forall //.
Qed.

Lemma wp_prim_mono e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → wp_prim e Φ ⊢ wp_prim e Ψ.
Proof.
  iIntros (HΦ) "Hwp". iApply (wp_prim_mono_aux with "Hwp"). iIntros "!>" (v) "HΦ".
  by rewrite HΦ.
Qed.

Lemma pure_ctx_step_reducible_or_blocked_own e1 e2 h Σ :
  pure_ctx_step e1 e2 → reducible_or_blocked_own e1 h Σ.
Proof.
  intros [k e1' e2' Hk Hstep].
  left. do 4 eexists. apply (Prim_step k); eauto using head_step.
Qed.

Lemma wp_prim_pure_step e1 e2 Φ :
  pure_ctx_step e1 e2 →
  wp_prim e2 Φ ⊢ wp_prim e1 Φ.
Proof.
  intros Hstep. apply aProp_entails; iIntros (Σ) "H". rewrite !wp_prim_unfold.
  rewrite (pure_ctx_step_not_val e1 e2) //. iExists Σ. iSplit; first done.
  iIntros (tid es h) "Hinv". iSplit.
  { eauto using pure_ctx_step_reducible_or_blocked_own. }
  iIntros (e2' h' es_new b Hstep') "!>". iExists Σ.
  destruct (pure_ctx_step_prim_step e1 e2 e2' h h' es_new b) as (->&->&->&->); [done..|].
  rewrite right_id_L. rewrite wp_prim_unfold /=; auto.
Qed.

Lemma reducible_or_blocked_own_ctx k e h Σ :
  ctx k → reducible_or_blocked_own e h Σ → reducible_or_blocked_own (k e) h Σ.
Proof.
  intros Hctx [Hred | (l & Φ & Hbl & HΣ)].
  - left. destruct Hred as (e' & h' & es & b & Hstep).
    unfold reducible.
    do 4 eexists. eauto using prim_step_ctx.
  - right. destruct Hbl as (k' & e' & Hctx' & -> & Hbl).
    eexists _,_. split; eauto.
    unfold blocked.
    exists (k ∘ k').
    eauto using ctx_compose.
Qed.

Local Program Definition Ψbind k φ : expr → (val -d> aProp) -n> aProp := λ e,
  (λne (Φ : val -d> aProp), (□ (∀ v : val, Φ v -∗ wp_prim (k (Val v)) φ) -∗ wp_prim (k e) φ)%I).
Next Obligation. solve_proper. Qed.

Local Lemma wp_prim_bind_aux k φ e :
   ctx k →
   ∀ Φ, wp_prim e Φ -∗ □ (∀ v, Φ v -∗ wp_prim (k (Val v)) φ) -∗ wp_prim (k e) φ.
Proof.
  iIntros (Hctx Φ).
  replace ( □ (∀ v : val, Φ v -∗ wp_prim (k (Val v)) φ) -∗ wp_prim (k e) φ)%I with (Ψbind k φ e Φ) by done.
  iRevert (e Φ).
  iApply wp_prim_ind. 
  iIntros "!>" (e1 Φ1) "HInd Hv".
  rewrite Ind_wp_unfold /Ψbind /= wp_prim_unfold.
  destruct (to_val (k e1)) as [v1|] eqn:Heq.
  - assert (is_Some (to_val (k e1))) by (by eexists).
    set H2 := (to_val_ctx_is_Some_id k e1 Hctx H).
    rewrite H2 /= in Heq. rewrite Heq.
    iMod "HInd". iApply wp_prim_val_inv.
    iSpecialize ("Hv" $! v1 with "[HInd]") ; first done.
    rewrite H2 /= //.
  - destruct (to_val e1) as [v2|] eqn:Heq2.
    + iAssert ( AProp (λ Σ : outEdges, ∀ (tid : nat) (es : list expr) (h : heap), ▷ inv' (es, h) tid Σ → ◇ (⌜reducible_or_blocked_own (k e1) h Σ⌝ ∧ ∀ (e' : expr) (h' : heap) (es_new : list expr) (b : bool), ⌜prim_step (k e1) h e' h' es_new b⌝ → ∃ Σtid : outEdges, ▷ inv' (es ++ es_new, h') tid Σtid ∧ ▷?b aProp_at (wp_prim e' φ) Σtid)) ≡ wp_prim (k e1) φ)%I as "H2".
      { rewrite wp_prim_unfold Heq //. }
      iRewrite "H2".
      iMod "HInd".
      iSpecialize ("Hv" $! v2 with "[HInd]") ; first done.
      rewrite to_val_Val in Heq2.
      rewrite Heq2 //.
    + iApply AProp_mono; last first.
      * iApply AProp_sep_persistent. iFrame.
      * iIntros (Σ) "[IH Hv] /=".
        iIntros (tid es h) "Hinv".
        iMod ("IH" with "Hinv") as "[%Hred H]". iModIntro.
        iSplit.
        { iPureIntro. eauto using reducible_or_blocked_own_ctx. }
        iIntros (e' h' es_new b Hps).
        apply prim_step_ctx_inv in Hps as (e'' & Hps & ->); [|done..].
        iDestruct ("H" with "[//]") as (Σtid) "[H1 H2]".
        iExists Σtid. iSplit; first (iNext ; by iApply inv'_ind_inv'). iModIntro.
        rewrite aProp_at_and.
        iDestruct "H2" as "[H2 H3]".
        rewrite !aProp_at_wand.
        iAssert (⌜ Σtid ##ₘ ∅ ⌝)%I as "Hdisj".
        { iPureIntro. apply map_disjoint_empty_r. }
        iSpecialize ("H2" with "[//]").
        rewrite map_union_empty.
        iApply "H2".
        rewrite aProp_at_intuitionistically.
        by iFrame.
Qed.

Lemma wp_prim_bind k Φ e :
  ctx k →
  wp_prim e (λ v, wp_prim (k $ Val v) Φ) ⊢
  wp_prim (k e) Φ.
Proof.
  iIntros (Hctx) "Hwp".
  iApply (wp_prim_bind_aux with "Hwp") ; first done.
  by iIntros "!>" (v) "HΦ".
Qed.

Lemma reducible_send h l v :
  h !! l = Some (ChanHV None) →
  reducible (Send (Val (LitV (LitLoc l))) (Val v)) h.
Proof. do 4 eexists. apply (Prim_step id); eauto using ctx, head_step. Qed.

Lemma prim_step_send_inv l v h e' h' es_new b :
  prim_step (Send (Val (LitV (LitLoc l))) (Val v)) h e' h' es_new b →
  e' = Val (LitV LitUnit) ∧ h !! l = Some (ChanHV None) ∧
  h' = <[l:=ChanHV (Some v)]> h ∧ es_new = [] ∧ b = true.
Proof. intros Hstep. by inv_prim_step Hstep. Qed.

Lemma wp_prim_send l v Φ R :
  own_chan l (MiniProt ASend Φ) ∗ ▷ Φ v ∗ ▷ R ⊢
  wp_prim (Send (Val (LitV (LitLoc l))) (Val v)) (λ v, ⌜⌜ v = LitV LitUnit ⌝⌝ ∗ R) .
Proof.
  eapply aProp_entails. iIntros (Σ) "H".
  rewrite aProp_at_sep_own_chan. iDestruct "H" as ([a Ψ] Hl) "[Heq H]".
  iDestruct "H" as (Σ1 Σ2 Hun Hdisj) "[HΦ HR]".
  rewrite wp_prim_unfold /=. iExists Σ. iSplit; first done.
  rewrite miniprot_equivI /=. iDestruct "Heq" as "[>-> HΨΦ]".
  iIntros (tid es h) "#Hinv". iSplit.
  { 
    iApply timeless. iModIntro. iClear (R Φ) "HR HΨΦ HΦ".
    iLeft. rewrite inv'_unfold /ginv.
    iDestruct "Hinv" as (g Hwf) "Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //. iDestruct "Hthr" as "[_ HΣ]".
    rewrite gmap_equivI.
    iSpecialize ("HΣ" $! (Chan l)).
    rewrite Hl internal_eq_sym out_edges_in_labels.
    iDestruct "HΣ" as (X) "HΣ".
    iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
    iRewrite "HΣ" in "Hchan".
    destruct (h !! l) as [[[w|]|w]|] eqn:Heq; simpl.
    - iDestruct "Hchan" as (Φ') "[Hinl Hchan]".
      rewrite multiset_singleton_disj_union_singletonI sum_equivI /=.
      rewrite miniprot_equivI /=.
      by iDestruct "Hinl" as "[[% _] _]".
    - auto using reducible_send.
    - iDestruct "Hchan" as "[Hchan1 Hchan2]".
      rewrite aProp_at_internal_eq multiset_singleton_disj_union_singletonI.
      iDestruct "Hchan2" as "[Hchan2 _]".
      rewrite sum_equivI //.
    - iDestruct "Hchan" as "[_ %Hinl]".
      apply multiset_disj_union_eq_empty in Hinl
        as [[]%multiset_singleton_neq_empty _]. }
  iIntros (e' h' b es_new (->&Hhl&->&->&->)%prim_step_send_inv) "!>".
  rewrite right_id_L.
  iExists Σ2;  iSplit; last first.
  { rewrite wp_prim_unfold /=.
    rewrite aProp_at_except_0 aProp_at_sep_affinely_l aProp_at_pure. auto. }
  iModIntro.
  iRewrite -("HΨΦ" $! v) in "HΦ".
  iClear (R Φ) "HR". rewrite !inv'_unfold /ginv.
  iDestruct "Hinv" as (g Hwf) "Hinv".
  iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
  rewrite decide_True //.
  iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
  iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
  rewrite Hhl /=. iDestruct "Hchan" as (Φ Hout) "Hchan".
  iDestruct (exchange_dealloc g (Thread tid) (Chan l)
              Σ2 Σ1 (inr (MiniProt ASend Ψ)) with "[]") as "Hgraph"; try done.
  { iRewrite -"HΣ". rewrite Hl. iSplit; eauto.
    rewrite Hun Hout. rewrite (right_id ∅).
    rewrite map_union_comm //. }
  iDestruct "Hgraph" as (g' Hwf' _) "(HΣ2 & HΣ1 & Hout & Hin & Hin_ne)".
  iExists g'. iSplit; first done.
  iIntros (v'). iSpecialize ("Hinv" $! v').
  destruct v' as [i'|l']; first case_decide; simplify_eq/=.
  - iSplit.
    + iDestruct "Hinv" as "[[%H1 %H2] Hinv]". iSplit; last done.
      rewrite -!multiset_empty_equiv_eq. iApply discrete_eq.
      iRewrite ("Hin_ne" $! (Thread i') with "[//]"). by rewrite Hinltid.
    + by iRewrite "HΣ2".
  - iRewrite ("Hout" $! (Thread i') with "[%]"); first naive_solver.
    by iRewrite ("Hin_ne" $! (Thread i') with "[//]").
  - rewrite lookup_insert_spec. case_decide; simplify_eq/=.
    + rewrite aProp_at_exist. iExists Ψ.
      rewrite aProp_at_sep_affinely_l !aProp_at_internal_eq. iSplit.
      * iApply "Hin". iRewrite "Hchan".
        iDestruct (out_edges_in_labels g (Thread tid) (Chan l') with "[]") as (X) "HHH".
        { iRewrite -"HΣ". rewrite Hl. done. }
        iRewrite "Hchan" in "HHH".
        iDestruct (internal_eq_sym with "HHH") as "H4".
        iDestruct (multiset_singleton_disj_union_singletonsI with "H4") as "{H4} [[H5 H6]|[H5 H6]]";
          rewrite ?sum_equivI;
          iDestruct (miniprot_equivI with "H5") as "[% H7]"; simplify_eq/=.
        iAssert (∀ a, MiniProt a Ψ ≡ MiniProt a Φ)%I as "Hprot".
        { iIntros (a). iApply miniprot_equivI. auto. }
        iRewrite ("Hprot" $! ASend). by iRewrite -("Hprot" $! ARecv).
      * by iRewrite "HΣ1".
    + iRewrite ("Hout" $! (Chan l') with "[%]"); first naive_solver.
      by iRewrite ("Hin_ne"$! (Chan l')  with "[%]"); first naive_solver.
Qed.

Lemma reducible_or_blocked_own_recv h l mv Σ Ψ :
  h !! l = Some (ChanHV mv) →
  Σ !! Chan l = Some (inr (MiniProt ARecv Ψ)) →
  reducible_or_blocked_own (Recv (Val (LitV (LitLoc l)))) h Σ.
Proof.
  intros. destruct mv as [v|].
  - left. do 4 eexists. apply (Prim_step id); eauto using ctx, head_step.
  - right. do 2 eexists. split; last done.
    exists id; eauto using ctx, head_blocked.
Qed.

Lemma prim_step_recv_inv l h e' h' es_new b :
  prim_step (Recv (Val (LitV (LitLoc l)))) h e' h' es_new b →
  ∃ v, e' = Val v ∧ h !! l = Some (ChanHV (Some v)) ∧
       h' = delete l h ∧ es_new = [] ∧ b = true.
Proof. intros Hstep. inv_prim_step Hstep; eexists ; eauto. Qed.

Lemma wp_prim_recv l Φ R :
  own_chan l (MiniProt ARecv Φ) ∗ ▷ R ⊢
  wp_prim (Recv (Val (LitV (LitLoc l)))) (λ v, Φ v ∗ R).
Proof.
  eapply aProp_entails; iIntros (Σ) "H".
  rewrite aProp_at_sep_own_chan. iDestruct "H" as ([a Ψ] Hl) "[Heq HR]".
  rewrite wp_prim_unfold /=. iExists Σ. iSplit; first done.
  rewrite miniprot_equivI /=. iDestruct "Heq" as "[>-> Heq]".
  iIntros (tid es h) "Hinv". iSplit.
  { iApply timeless. iModIntro. iClear (R Φ) "HR Heq".
    rewrite inv'_unfold /ginv.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //.
    iDestruct "Hthr" as "[_ HΣ]".
    rewrite gmap_equivI.
    iSpecialize ("HΣ" $! (Chan l)).
    rewrite Hl.
    rewrite internal_eq_sym.
    rewrite out_edges_in_labels.
    iDestruct "HΣ" as (X) "HΣ".
    iDestruct ("Hinv" $! (Chan l)) as "Hchan". simpl.
    iRewrite "HΣ" in "Hchan".
    destruct (h !! l) as [[mv|w]|] eqn:Heq; simplify_eq/=.
    - eauto using reducible_or_blocked_own_recv.
    - iDestruct "Hchan" as "[Hchan1 Hchan2]".
      rewrite aProp_at_internal_eq multiset_singleton_disj_union_singletonI.
      iDestruct "Hchan2" as "[Hchan2 _]".
      rewrite sum_equivI //.
    - iDestruct "Hchan" as "[_ %Hinl]".
      apply multiset_disj_union_eq_empty in Hinl
        as [[]%multiset_singleton_neq_empty _]. }
  iIntros (e' h' b es_new (v&->&Hhl&->&->&->)%prim_step_recv_inv) "!>".
  rewrite right_id_L.
  rewrite inv'_unfold /ginv /=.
  
  iAssert (
  (▷ ∃ Σtid : outEdges, inv' (es, delete l h) tid Σtid ∧ aProp_at (wp_prim (Val v) (λ v0 : val, Φ v0 ∗ R)) Σtid) -∗
∃ Σtid : outEdges, ▷ inv' (es, delete l h) tid Σtid ∧ ▷ aProp_at (wp_prim (Val v) (λ v0 : val, Φ v0 ∗ R)) Σtid
  )%I as "H".
  { iIntros "H". rewrite later_exist.
    iDestruct "H" as (Σtid) "[HΣtid Hwp]".
    iExists Σtid. iFrame.
  }
  iApply "H". iClear "H".
  iModIntro.
  iDestruct "Hinv" as (g Hwf) "#Hinv".
  iExists (delete (Chan l) Σ ∪ out_edges g (Chan l)).
  iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
  rewrite decide_True //.
  iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
  iPoseProof "HΣ" as "HΣ'".
  rewrite {1}gmap_equivI.
  iSpecialize ("HΣ" $! (Chan l)).
  rewrite Hl.
  rewrite internal_eq_sym.
  iPoseProof "HΣ" as "HΣ''".
  rewrite {1}out_edges_in_labels.
  iDestruct "HΣ" as (X) "HΣ".
  iDestruct ("Hinv" $! (Chan l)) as "Hchan". rewrite /= Hhl /=.
  iDestruct "Hchan" as (Φ') "[Hinl Hchan]".
  iRewrite "HΣ" in "Hinl".
  rewrite multiset_singleton_disj_union_singletonI.
  iDestruct "Hinl" as "[Hinl ->]".
  rewrite sum_equivI miniprot_equivI /=.
  iDestruct "Hinl" as "[_ Hinl]".

  iAssert ⌜ delete (Chan l) Σ ##ₘ out_edges g (Chan l) ⌝%I as %Hdisj.
  { iAssert ⌜ edge g (Thread tid) (Chan l) ⌝%I as "%Hedge".
    { unfold edge. iRewrite "HΣ''". done. }
    eapply edge_out_disjoint in Hedge; eauto.
    iRewrite "HΣ'". iPureIntro. by apply map_disjoint_delete_l. }

  iSplit; last first.
  { rewrite wp_prim_unfold /=.
    rewrite (comm (∗))%I. rewrite aProp_at_except_0 aProp_at_sep. iModIntro.
    iExists _, _. do 3 (iSplit; [by eauto|]).
    iRewrite -("Heq" $! v). by iRewrite ("Hinl" $! v). }
  iDestruct (exchange_dealloc g (Thread tid) (Chan l)
              (delete (Chan l) (out_edges g (Thread tid)) ∪ out_edges g (Chan l))
              ∅ (inr (MiniProt ARecv Ψ)) with "[]") as "Hgraph"; first done.
  { solve_map_disjoint. }
  { iSplit; first done. rewrite !(right_id ∅) //. }
  iDestruct "Hgraph" as (g' Hwf' _) "(Hout1 & Hout2 & HH1 & HH2 & HH3)".
  iExists g'. iSplit; first done.
  iIntros (v').
  iSpecialize ("Hinv" $! v').
  destruct v' as [i'|l']; first case_decide; subst.
  - iSplit.
    + iDestruct "Hinv" as "[[%H1 %H2] Hinv]". iSplit; last done.
      rewrite -!multiset_empty_equiv_eq.
      iApply discrete_eq.
      iRewrite ("HH3" $! (Thread i') with "[//]"). by rewrite Hinltid.
    + iRewrite "Hout1". iRewrite "HΣ'". done.
  - iRewrite ("HH1" $! (Thread i') with "[%]"); first naive_solver.
    by iRewrite ("HH3" $! (Thread i') with "[//]").
  - rewrite /= lookup_delete_spec. case_decide; simplify_eq/=.
    + rewrite !aProp_at_affinely aProp_at_pure.
      iSplit; eauto.
      rewrite -!multiset_empty_equiv_eq.
      iApply discrete_eq.
      by iApply "HH2".
    + iRewrite ("HH1" $! (Chan l') with "[%]"); first naive_solver.
      iRewrite ("HH3" $! (Chan l') with "[%]"); naive_solver.
Qed.

Lemma reducible_or_blocked_own_fork_chan f h Σ :
  reducible_or_blocked_own (ForkChan (Val f)) h Σ.
Proof.
  left. eexists _, (<[fresh (dom h):=_]> h), _, _.
  eapply (Prim_step id); eauto using ctx.
  constructor.
  (* apply not_elem_of_dom, is_fresh. *)
Qed.
Lemma prim_step_fork_heap_val_inv f h e' h' es_new b :
  prim_step (ForkChan (Val f)) h e' h' es_new b →
  ∃ l, e' = Val (LitV (LitLoc l)) ∧ h !! l = None ∧ h' = <[l:=ChanHV None]> h ∧
       es_new = [App (Val f) (Val (LitV (LitLoc l)))] ∧ b = true.
Proof.
  intros Hstep. inv_prim_step Hstep; eexists ; repeat split .
  apply not_elem_of_dom, is_fresh.
Qed.

Lemma wp_prim_fork f p R :
  ▷ (∀ l, own_chan l (dual p) -∗ wp_prim (App (Val f) (Val (LitV (LitLoc l)))) (λ _, emp)) ∗ ▷ R ⊢
  wp_prim (ForkChan (Val f)) (λ v, (∃ l, ⌜⌜ v = LitV (LitLoc l) ⌝⌝ ∗ own_chan l p) ∗ R).
Proof.
  eapply aProp_entails. intros Σ.
  iDestruct 1 as (Σ1 Σ2 -> Hdisj) "[H HR]".
  rewrite wp_prim_unfold /=. iExists _. iSplit; first done.
  iIntros (tid es h) "#Hinv". iSplit.
  { auto using reducible_or_blocked_own_fork_chan. }
  iIntros (e' h' es_new b  (l&->&Hhl&->&->&->)%prim_step_fork_heap_val_inv).
  iAssert (◇ ⌜Σ1 ∪ Σ2 ##ₘ {[Chan l := inr (dual p)]}⌝)%I as "Hdisj12".
  { iApply timeless. iNext.
    rewrite inv'_unfold /ginv.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //=.
    iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
    iAssert (⌜ out_edges g (Thread tid) !! Chan l = None ⌝)%I as "%Hout".
    { destruct (out_edges g (Thread tid) !! Chan l) eqn:Heqn; try done.
      iDestruct (out_edges_in_labels g (Thread tid) (Chan l) with "[]") as (X) "HHH".
      { rewrite Heqn //. }
      iSpecialize ("Hinv" $! (Chan l)).
      rewrite Hhl /=.
      rewrite aProp_at_affinely aProp_at_pure.
      iDestruct "Hinv" as "[_ ->]".
      by iDestruct "HHH" as %?%symmetry%multiset_empty_equiv_eq. }
    iRewrite "HΣ".
    iPureIntro. solve_map_disjoint. }
  iMod "Hdisj12" as %Hdisj12.
  assert (Σ1 ##ₘ {[Chan l := inr (dual p)]}) as Hdisj1 by solve_map_disjoint.
  assert ({[Chan l := inr p ]} ##ₘ Σ2) as Hdisj2 by solve_map_disjoint.
  iExists ({[Chan l := inr p ]} ∪ Σ2).
  iSplit; last first.
  { rewrite wp_prim_unfold.
    rewrite aProp_at_except_0 aProp_at_sep /=. iModIntro.
    iExists _,_. iSplit; first done.
    iSplit; first done.
    iModIntro.
    iSplit; eauto.
    rewrite aProp_at_exist. iExists _.
    rewrite aProp_at_sep_affinely_l.
    rewrite aProp_at_pure. iSplit; first done.
    rewrite aProp_at_own_chan. eauto.
  }
  iClear "HR". clear R. iIntros "!> !>".
  rewrite !inv'_unfold /ginv.
  iDestruct "Hinv" as (g Hwf) "#Hinv".
  iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
  rewrite decide_True //.
  iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
  rewrite internal_eq_sym.
  iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
  rewrite Hhl /=.
  iDestruct "Hchan" as "[%Hchanin %Hchanout]".
  iDestruct ("Hinv" $! (Thread (length es))) as "Hthr2".
  case_decide; subst.
  {
    iSpecialize ("Hinv" $! (Thread (length es))).
    rewrite decide_True //.
    iDestruct "Hinv" as "[_ ?]". simpl in *. lia.
  }
  rewrite lookup_ge_None_2; last done. simpl.
  iDestruct "Hthr2" as "[%Hthr2out %Hthr2in]".
  iDestruct (move_fork g (Thread tid) (Chan l) (Thread (length es))
              _ _ (inr p) (inr (dual p)) with "HΣ") as "Hgraph"; try done.
  { naive_solver. }
  iDestruct "Hgraph" as (g' Hwf') "(Hout1 & Hout2 & Hout3 & Hin1 & Hout & Hin2)".
  iExists g'. iSplit; first done.
  iIntros (v').
  iSpecialize ("Hinv" $! v').
  iSpecialize ("Hout" $! v').
  iSpecialize ("Hin2" $! v').
  destruct v' as [i'|l']; first case_decide; subst.
  - iSplit.
    + iSplit; last first.
      { rewrite length_app /=. iPureIntro. simpl in *. lia. }
      rewrite -!multiset_empty_equiv_eq.
      iApply discrete_eq.
      iRewrite ("Hin2" with "[//]"). by rewrite Hinltid.
    + iRewrite "Hout1". done.
  - destruct (decide (i' = length es)); subst.
    + rewrite lookup_app_r //.
      replace (length es - length es) with 0 by lia. simpl.
      rewrite aProp_at_sep_affinely_l aProp_at_pure.
      iSplit.
      * rewrite -!multiset_empty_equiv_eq.
        iApply discrete_eq.
        iRewrite ("Hin2" with "[//]").
        rewrite Hthr2in //.
      * iSpecialize ("H" $! l).
        rewrite aProp_at_wand.
        iSpecialize ("H" $! {[ Chan l := inr (dual p) ]}).
        iRewrite "Hout3".
        rewrite !(map_union_comm Σ1); try done.
        iApply "H"; first done.
        rewrite aProp_at_own_chan. eauto.
    + destruct (decide (i' < length es)).
      * rewrite lookup_app_l; last lia.
        iRewrite ("Hin2" with "[//]").
        iRewrite ("Hout" with "[]").
        { iPureIntro. split_and!; intro; simplify_eq. }
        done.
      * rewrite lookup_app_r; last lia.
        destruct (i' - length es) eqn:E; try lia. simpl.
        rewrite lookup_ge_None_2; last lia. simpl.
        rewrite !aProp_at_affinely !aProp_at_pure.
        iDestruct "Hinv" as "[Hinv1 %Hinv2]".
        iSplit.
        { iRewrite ("Hout" with "[]"); last done.
          iPureIntro. split_and!; intro; simplify_eq. }
        simpl in *.
        rewrite -!multiset_empty_equiv_eq.
        iApply discrete_eq.
        iRewrite ("Hin2" with "[//]").
        rewrite Hinv2 //.
  - rewrite lookup_insert_spec. case_decide; subst; simpl.
    + rewrite aProp_at_exist. destruct p. iExists prot_pred.
      rewrite aProp_at_affinely.
      iSplit; eauto.
      iRewrite "Hin1".
      rewrite aProp_at_internal_eq.
      destruct prot_action; eauto.
      rewrite /dual. simpl.
      rewrite comm //.
    + iRewrite ("Hout" with "[]").
      { iPureIntro. split_and!; intro; simplify_eq. }
      iRewrite ("Hin2" with "[]").
      { iPureIntro. intro. simplify_eq. }
      done.
Qed.

Lemma alloc_reducible v h :
  reducible (Alloc (Val v)) h.
Proof.
  eexists _, (<[ fresh (dom h) := RefHV v ]> h), _, _.
  apply (Prim_step id); eauto using ctx.
  eapply AllocS.
  (* apply not_elem_of_dom, is_fresh. *)
Qed.

Lemma wp_prim_alloc R v :
  (*▷*) R ⊢ wp_prim (Alloc (Val v)) (λ w, (∃ l, ⌜⌜ w = LitV (LitLoc l) ⌝⌝ ∗ l ↦ v) ∗ R).
Proof.
  eapply aProp_entails. iIntros (Σ) "H".
  rewrite wp_prim_unfold /=. iExists _. iSplit; first done.
  iIntros (tid es h) "#Hinv". iSplit.
  { iLeft. eauto using alloc_reducible. }
  iIntros (e' h' es_new b Hstep).
  inv_prim_step Hstep; simplify_eq/=.
  iExists ({[ _ := _ ]} ∪ Σ). rewrite right_id.
  rewrite inv'_unfold /ginv.
  iSplit. {
    iModIntro.
    iModIntro.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //.
    iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]". simpl in *.
    set l:= fresh (dom h).
    iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
    assert (h !! l = None) as H1.
    { apply not_elem_of_dom, is_fresh. }
    rewrite H1 /=.
    iDestruct "Hchan" as "[%Houtchan %Hinchan]".

    rewrite inv'_unfold /ginv.
    iDestruct (ref_alloc g (Thread tid) (Chan l)) as "Hgraph"; try done.
    iDestruct "Hgraph" as (g' Hwf') "(Hout1 & Hout & Hin1 & Hin)".
    iExists g'. iSplit; first done.
    iIntros (v').
    iSpecialize ("Hinv" $! v').
    destruct v' as [i'|l']; first case_decide; subst.
    - iSplit.
      + iDestruct "Hinv" as "[[%H1' %H2] Hinv]". iSplit; last done.
        rewrite -!multiset_empty_equiv_eq.
        iApply discrete_eq.
        iRewrite ("Hin" $! (Thread i') with "[//]"). by rewrite Hinltid.
      + iRewrite "Hout1". iRewrite "HΣ". done.
    - simpl.
      iRewrite ("Hout" $! (Thread i') with "[%]"); first naive_solver.
      iRewrite ("Hin" $! (Thread i') with "[//]"). done.
    - simpl.
      rewrite lookup_insert_spec. case_decide; subst; simpl.
      + rewrite aProp_at_affinely aProp_at_internal_eq.
        iRewrite ("Hout" $! (Chan l) with "[%]"); first naive_solver.
        rewrite Houtchan. iSplit; first done.
        done.
      + iRewrite ("Hout" $! (Chan l') with "[%]"); first naive_solver.
        iRewrite ("Hin" $! (Chan l') with "[%]"); first naive_solver.
        done.
  }
  
  rewrite later_exist.
  iDestruct "Hinv" as (g) "[#Hwf #Hinv]".
  iMod "Hwf" as %Hwf.
  rewrite later_forall.

  iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
  rewrite decide_True //.

  rewrite later_and.
  iDestruct "Hthr" as "[Hp HΣ]". simpl in *.
  iMod "Hp" as %[Hinlen Hlen].
  set l:= fresh (dom h).
  iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
  assert (h !! l = None) as ->.
  { apply not_elem_of_dom, is_fresh. }
  rewrite !aProp_at_affinely later_and.
  iDestruct "Hchan" as "[Houtchan Hinchan]".
  rewrite !timeless.
  iMod "Houtchan" as %Houtchan.
  rewrite wp_prim_unfold /=.
  rewrite aProp_at_except_0 aProp_at_sep.
  iModIntro.
  iExists _,_. iSplit; first done.
  iSplit.
  { 
    iApply timeless.
    iModIntro.
    iPure "Hinchan" as Hinchan.
    assert (in_labels g (Chan l) = ∅) as HH by rewrite Hinchan //.
    iRewrite "HΣ". iPureIntro.
    eapply (no_in_labels_no_out_edge _ (Thread tid)) in HH.
    solve_map_disjoint. }
  iSplit; last done.
  rewrite aProp_at_exist. iExists _.
  rewrite aProp_at_sep_affinely_l.
  rewrite aProp_at_pure. iSplit. 
  { rewrite aProp_at_pure //. }
  rewrite aProp_at_own_ref //.
  Qed.


Lemma load_reducible l v h :
  h !! l = Some (RefHV v) →
  reducible (Load (Val (LitV (LitLoc l)))) h.
Proof.
  intros. do 4 eexists. apply (Prim_step id); eauto using ctx, head_step.
Qed.

Lemma wp_prim_load l R v :
  l ↦ v ∗ (*▷*) R ⊢ wp_prim (Load (Val (LitV (LitLoc l)))) (λ w, (⌜⌜ w = v ⌝⌝ ∗ l ↦ v) ∗ R).
Proof.
  eapply aProp_entails. iIntros (Σ) "H".
  rewrite wp_prim_unfold /=. iExists _. iSplit; first done.
  iIntros (tid es h) "#Hinv". iSplit.
  {
    iApply timeless. iNext. iLeft.
    iDestruct "H" as (Σ1 Σ2 -> Hdisj) "[H HR]".
    rewrite aProp_at_own_ref.
    iDestruct "H" as %->.
    rewrite inv'_unfold /ginv.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //.
    iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
    iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
    iAssert (out_edges g (Thread tid) !! Chan l ≡ Some (inl v))%I as "Hoe".
    { iRewrite -"HΣ". rewrite lookup_union_l ?lookup_singleton //. solve_map_disjoint. }
    iDestruct (out_edges_in_labels with "Hoe") as (X) "HHH".
    iRewrite "HHH" in "Hchan". iClear "HHH Hoe HΣ".
    destruct (h !! l) as [[[]|w]|] eqn:Heq; simpl.
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite multiset_singleton_disj_union_singletonI sum_equivI /=.
      by iDestruct "Hinl" as "[%A B]".
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite aProp_at_internal_eq multiset_singleton_disj_union_singletonsI.
      rewrite !sum_equivI.
      by iDestruct "Hchan" as "[[%A _]|[%A _]]".
    - eauto using load_reducible.
    - iDestruct "Hchan" as "[Hchan1 %Hchan2]".
      by apply multiset_disj_union_eq_empty in Hchan2 as []. }
  iIntros (e' h' es_new b Hps) "!>". inv_prim_step Hps.
  iExists Σ. rewrite right_id. iSplit; first done.
  rewrite wp_prim_unfold /=.
  iDestruct "H" as (Σ1 Σ2 -> Hdisj) "[H HR]".
  rewrite aProp_at_except_0 aProp_at_sep. 
  iExists _,_. iSplit; first done.
  iSplit; first done.
  iSplit; last done.
  rewrite aProp_at_sep_affinely_l.
  iSplit; last done.
  rewrite aProp_at_pure.
  rewrite inv'_unfold /ginv.
  rewrite later_exist.
  iDestruct "Hinv" as (g ) "[Hwf #Hinv]".
  iDestruct ("Hinv" $! (Chan l)) as "Hchan". simpl.
  rewrite H1 /=.
  iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
  rewrite decide_True //.
  iDestruct "Hthr" as "[Hinltidlen HΣ]".
  rewrite !timeless.
  iMod "Hinltidlen" as %Hinltid.
  iMod "Hwf" as %Hwf.
  rewrite -timeless.
  iModIntro.
  rewrite aProp_at_own_ref.
  iDestruct "H" as %->.
  rewrite aProp_at_affinely.
  rewrite aProp_at_internal_eq.
  iDestruct "Hchan" as "[%Houtchan Hinchan]".
  iAssert (out_edges g (Thread tid) !! Chan l ≡ Some (inl v))%I as "Hoe".
  { iRewrite -"HΣ". rewrite lookup_union_l ?lookup_singleton //. solve_map_disjoint. }
  iDestruct (out_edges_in_labels with "Hoe") as (X) "HHH".
  iRewrite "Hinchan" in "HHH".
  iClear "Hinchan HΣ Hoe".
  rewrite internal_eq_sym.
  iDestruct (multiset_singleton_disj_union_singletonI with "HHH") as "[%H _]".
  inversion H. simplify_eq. done.
Qed.

Lemma store_reducible l v w h :
  h !! l = Some (RefHV v) →
  reducible (Store (Val (LitV (LitLoc l))) (Val w)) h.
Proof.
  intros. do 4 eexists. apply (Prim_step id); eauto using ctx, head_step.
Qed.

Lemma wp_prim_store l v' R v :
  l ↦ v ∗ (*▷*) R ⊢ wp_prim (Store (Val (LitV (LitLoc l))) (Val v')) (λ w, (⌜⌜ w = LitV LitUnit ⌝⌝ ∗ l ↦ v') ∗ R).
Proof.
  eapply aProp_entails. iIntros (Σ) "H".
  rewrite wp_prim_unfold /=. iExists _. iSplit; first done.
  iIntros (tid es h) "#Hinv". iSplit.
  {
    iApply timeless. iNext. iLeft.
    iDestruct "H" as (Σ1 Σ2 -> Hdisj) "[H HR]".
    rewrite aProp_at_own_ref.
    iDestruct "H" as %->.
    rewrite inv'_unfold /ginv.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //.
    iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
    iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
    iAssert (out_edges g (Thread tid) !! Chan l ≡ Some (inl v))%I as "Hoe".
    { iRewrite -"HΣ". rewrite lookup_union_l ?lookup_singleton //. solve_map_disjoint. }
    iDestruct (out_edges_in_labels with "Hoe") as (X) "HHH".
    iRewrite "HHH" in "Hchan". iClear "HHH Hoe HΣ".
    destruct (h !! l) as [[[]|w]|] eqn:Heq; simpl.
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite multiset_singleton_disj_union_singletonI sum_equivI /=.
      by iDestruct "Hinl" as "[%A B]".
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite aProp_at_internal_eq multiset_singleton_disj_union_singletonsI.
      rewrite !sum_equivI.
      by iDestruct "Hchan" as "[[%A _]|[%A _]]".
    - eauto using store_reducible.
    - iDestruct "Hchan" as "[Hchan1 %Hchan2]".
      by apply multiset_disj_union_eq_empty in Hchan2 as []. }
  iIntros (e' h' es_new b Hps) "!>". inv_prim_step Hps.
  iDestruct "H" as (Σ1 Σ2 -> Hdisj) "[H HR]".
  rewrite aProp_at_own_ref.
  iDestruct "H" as %->.
  iExists ({[ Chan l := inl v' ]} ∪ Σ2). rewrite right_id.
  iSplit. {
    rewrite !inv'_unfold !/ginv.
    iModIntro.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //.
    iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
    iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
    iAssert (out_edges g (Thread tid) !! Chan l ≡ Some (inl v))%I as "Hoe".
    { iRewrite -"HΣ". rewrite lookup_union_l ?lookup_singleton //. solve_map_disjoint. }
    iDestruct (out_edges_in_labels with "Hoe") as (X) "HHH".
    iRewrite "HHH" in "Hchan".
    destruct (h !! l) as [[[]|w]|] eqn:Heq; simpl.
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite multiset_singleton_disj_union_singletonI sum_equivI /=.
      by iDestruct "Hinl" as "[%A B]".
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite aProp_at_internal_eq multiset_singleton_disj_union_singletonsI.
      rewrite !sum_equivI.
      by iDestruct "Hchan" as "[[%A _]|[%A _]]".
    - rewrite aProp_at_affinely aProp_at_internal_eq.
      iDestruct "Hchan" as "[Hchan1 Hchan2]".
      rewrite multiset_singleton_disj_union_singletonI sum_equivI /=.
      iDestruct "Hchan2" as "[HH ->]".
      iDestruct (exchange_relabel g (Thread tid) (Chan l) _ ∅ with "[]") as "Hgraph"; try done.
      { solve_map_disjoint. }
      { iRewrite "Hoe". iSplit; first done. rewrite !(right_id ∅) //. }
      iDestruct "Hgraph" as (g' Hwf') "(Hout1 & Hout2 & Hout3 & Hin1 & Hin2)".
      iExists g'. iSplit; first done.
      iIntros (u).
      iSpecialize ("Hinv" $! u).
      iSpecialize ("Hout3" $! u).
      iSpecialize ("Hin2" $! u).
      destruct u as [i'|l']; first case_decide; subst.
      + simpl in *. iSplit.
        { iSplit; last done.
          rewrite -!multiset_empty_equiv_eq.
          iApply discrete_eq.
          iRewrite ("Hin2" with "[//]"). by rewrite Hinltid. }
        iRewrite "Hout1".
        iDestruct "Hinv" as "[[%H1 %H2] Hinv]".
        iRewrite -"Hinv".
        iRewrite "Hchan1". rewrite !(right_id ∅).
        rewrite -!insert_union_singleton_l.
        rewrite delete_insert; last by solve_map_disjoint.
        done.
      + iRewrite ("Hout3" with "[]"). { iPureIntro. naive_solver. }
        iRewrite ("Hin2" with "[]"). { iPureIntro. naive_solver. }
        done.
      + rewrite lookup_insert_spec. case_decide; subst; simpl; try done.
        * rewrite aProp_at_affinely aProp_at_internal_eq.
          iSplit; first done.
          iDestruct ("Hin1" $! ∅ with "[]") as "Hin1'".
          { rewrite right_id. done. }
          rewrite !right_id. done.
        * iRewrite ("Hout3" with "[]").
          { iPureIntro. naive_solver. }
          iRewrite ("Hin2" with "[]").
          { iPureIntro. naive_solver. }
          done.
    - iDestruct "Hchan" as "[Hchan1 %Hchan2]".
      by apply multiset_disj_union_eq_empty in Hchan2 as []. }
  rewrite wp_prim_unfold /=.
  rewrite aProp_at_except_0 aProp_at_sep. iModIntro.
  iExists _,_. iSplit; first done.
  iSplit. { iPureIntro. solve_map_disjoint. }
  iSplit; last done.
  rewrite aProp_at_sep_affinely_l.
  rewrite aProp_at_own_ref.
  iSplit; last done.
  rewrite aProp_at_pure.
  done.
Qed.

Lemma free_reducible l v h :
  h !! l = Some (RefHV v) →
  reducible (Free (Val (LitV (LitLoc l)))) h.
Proof.
  intros. do 4 eexists. apply (Prim_step id); eauto using ctx, head_step.
Qed.

Lemma wp_prim_free l R v :
  l ↦ v ∗ (*▷*) R ⊢ wp_prim (Free (Val (LitV (LitLoc l)))) (λ w, ⌜⌜ w = LitV LitUnit ⌝⌝ ∗ R).
Proof.
  eapply aProp_entails. iIntros (Σ) "H".
  rewrite wp_prim_unfold /=. iExists _. iSplit; first done.
  iIntros (tid es h) "#Hinv". iSplit.
  {
    iApply timeless. iNext. iLeft.
    iDestruct "H" as (Σ1 Σ2 -> Hdisj) "[H HR]".
    rewrite aProp_at_own_ref.
    iDestruct "H" as %->.
    rewrite inv'_unfold /ginv.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //.
    iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
    iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
    iAssert (out_edges g (Thread tid) !! Chan l ≡ Some (inl v))%I as "Hoe".
    { iRewrite -"HΣ". rewrite lookup_union_l ?lookup_singleton //. solve_map_disjoint. }
    iDestruct (out_edges_in_labels with "Hoe") as (X) "HHH".
    iRewrite "HHH" in "Hchan". iClear "HHH Hoe HΣ".
    destruct (h !! l) as [[[]|w]|] eqn:Heq; simpl.
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite multiset_singleton_disj_union_singletonI sum_equivI /=.
      by iDestruct "Hinl" as "[%A B]".
    - iDestruct "Hchan" as (Φ) "[Hinl Hchan]".
      rewrite aProp_at_internal_eq multiset_singleton_disj_union_singletonsI.
      rewrite !sum_equivI.
      by iDestruct "Hchan" as "[[%A _]|[%A _]]".
    - eauto using free_reducible.
    - iDestruct "Hchan" as "[Hchan1 %Hchan2]".
      by apply multiset_disj_union_eq_empty in Hchan2 as []. }
  iIntros (e' h' es_new b Hps) "!>". inv_prim_step Hps.
  iDestruct "H" as (Σ1 Σ2 -> Hdisj) "[H HR]".
  rewrite aProp_at_own_ref.
  iDestruct "H" as %->.
  iExists Σ2. rewrite right_id.
  rewrite inv'_unfold /ginv.
  iSplit.
  { 
    (* rewrite -later_and. *)
    iModIntro.
    iDestruct "Hinv" as (g Hwf) "#Hinv".
    iDestruct ("Hinv" $! (Thread tid)) as "Hthr".
    rewrite decide_True //.
    iDestruct "Hthr" as "[[%Hinltid %Hlen] HΣ]".
    iDestruct ("Hinv" $! (Chan l)) as "Hchan /=".
    rewrite H1 /=.
    rewrite aProp_at_affinely aProp_at_internal_eq.
    iDestruct "Hchan" as "[%Houtchan Hinchan]".
    rewrite map_empty_equiv_eq in Houtchan. simpl in *.

    iAssert (out_edges g (Thread tid) !! Chan l ≡ Some (inl v))%I as "Hoe".
      { iRewrite -"HΣ". rewrite lookup_union_l ?lookup_singleton //. solve_map_disjoint. }
    iDestruct (ref_free g (Thread tid) (Chan l) with "[]") as "Hgraph"; try done.
    { iDestruct (out_edges_in_labels with "Hoe") as (X) "HHH".
      iRewrite "Hoe". iSplit; first done.
      iRewrite "Hinchan".
      iRewrite "Hinchan" in "HHH". iClear "HΣ Hoe Hinchan".
      rewrite internal_eq_sym.
      rewrite multiset_singleton_disj_union_singletonI.
      iDestruct "HHH" as "[HHH ->]".
      iRewrite "HHH". done. }
    iDestruct "Hgraph" as (g' Hwf') "(Hout1 & Hin1 & Hout & Hin)".
    iExists g'. iSplit; first done.
    iIntros (u).
    iSpecialize ("Hinv" $! u).
    iSpecialize ("Hout" $! u).
    iSpecialize ("Hin" $! u).
    destruct u as [i'|l']; first case_decide; subst.
    + simpl in *. iSplit.
      { iSplit; last done.
        rewrite -!multiset_empty_equiv_eq.
        iApply discrete_eq.
        iRewrite ("Hin" with "[//]"). by rewrite Hinltid. }
      iRewrite "Hout1".
      iRewrite -"HΣ".
      rewrite -!insert_union_singleton_l.
      rewrite delete_insert; last by solve_map_disjoint.
      done.
    + iRewrite ("Hout" with "[]"). { iPureIntro. naive_solver. }
      iRewrite ("Hin" with "[]"). { iPureIntro. naive_solver. }
      done.
    + rewrite lookup_delete_spec. case_decide; subst; simpl; try done.
      * rewrite aProp_at_affinely aProp_at_pure.
        iSplit.
        { iRewrite ("Hout" with "[//]"). by rewrite Houtchan. }
        rewrite -!multiset_empty_equiv_eq -!discrete_eq.
        by iRewrite "Hin1".
      * iRewrite ("Hout" with "[]").
        { iPureIntro. naive_solver. }
        iRewrite ("Hin" with "[]").
        { iPureIntro. naive_solver. }
        done. }
  rewrite wp_prim_unfold /=.
  rewrite aProp_at_except_0 aProp_at_sep. iModIntro.
  iExists ∅,_. rewrite left_id. iSplit; first done.
  iSplit. { iPureIntro. solve_map_disjoint. }
  iSplit; last done.
  rewrite aProp_at_affinely aProp_at_pure //.
Qed.
