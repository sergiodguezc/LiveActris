From iris.bi.lib Require Import fixpoint_mono.
From dlfactris.lang Require Import metatheory.
From dlfactris.base_logic Require Export wp cgraph adequacy aprop.

(* Locally (thread-wise) Concurrently Weakly Normalizing *)
Definition locally_cwn σ : Prop :=
  ∀ tid e, σ.1 !! tid = Some e → 
  ∃ e' h', steps σ (<[tid:=e']>σ.1, h') ∧ (is_Some (to_val e') ∨ concurrent e').

(* Globally (system-wise) Concurrently Weakly Normalizing *)
Definition globally_cwn σ : Prop :=
  ∃ σ', steps σ σ' ∧ (∀ tid e, σ'.1 !! tid = Some e → is_Some (to_val e) ∨ concurrent e).

Program Definition from_pure (Ψ : outEdges → expr → (val -d> aProp) -n> siProp) :
  expr → (val -d> aProp) -n> aProp := λ e,
  (λne (Φ : val -d> aProp), AProp $ λ Σ, Ψ Σ e Φ)%I.
Next Obligation. solve_proper. Qed.

Lemma from_pure_sound (Ψ : outEdges -d> (expr -d> (val -d> aProp) -n> siProp)) e Φ Σ  :
 Ψ Σ e Φ ⊢ aProp_at ((from_pure Ψ) e Φ) Σ . 
Proof.
  iIntros "/= H"; iExists Σ; eauto.
Qed.

Lemma from_pure_complete_later (Ψ : outEdges → expr → (val -d> aProp) -n> siProp) e Φ Σ
  `{! ∀ n, Proper (dist n ==> eq ==> dist n) Ψ} :
  aProp_at ((from_pure Ψ) e Φ) Σ ⊢ ▷ Ψ Σ e Φ .
Proof.
  iIntros "/= H".
  iDestruct "H" as (Σ0) "[#HΣ #H]".
  rewrite excl_outEdges_injI; iNext.
  iAssert (Ψ Σ e ≡ Ψ Σ0 e)%I as "HΣ'".
  { by iRewrite "HΣ". }
  rewrite ofe_morO_equivI.
  by iRewrite ("HΣ'" $! Φ).
Qed.
  
Lemma wp_prim_ind_at_si_pure (Ψ : outEdges → expr → (val -d> aProp) -n> siProp) 
  `{! ∀ n, Proper (dist n ==> eq ==> dist n) Ψ} :
    (∀ e1 Φ1 Σ1, aProp_at (Ind_wp (from_pure Ψ) e1 Φ1) Σ1 → Ψ Σ1 e1 Φ1 ) ⊢
    ∀ e Φ Σ, aProp_at (wp_prim e Φ) Σ → ▷ Ψ Σ e Φ.
Proof.
  iIntros "#IH" (e Φ Σ) "Hwp". 
  rewrite -from_pure_complete_later //.
  iApply wp_prim_ind_at ; last done.
  iIntros (e1 Φ1 Σ1) "H".
  rewrite -from_pure_sound.
  by iApply "IH".
Qed.

Definition thread_cwn Σ : expr → (val -d> aProp) -n> siProp := λ e,
  (λne (Φ : val -d> aProp), 
    ∀ σ tid,
    ⌜ σ.1 !! tid = Some e ⌝ →
    ▷ inv' σ tid Σ → ◇ ⌜∃ (e' : expr) (h' : heap),
         steps σ (<[tid:=e']> σ.1, h') ∧ (is_Some (to_val e') ∨ concurrent e')⌝)%I.

(* A weakest precondition ensures that the thread is concurrently weakly normalizing *)
Lemma wp_thread_cwn :
  ∀ e Φ Σ, aProp_at (wp_prim e Φ) Σ ⊢ ▷ thread_cwn Σ e Φ.
Proof.
  iIntros (e Φ Σ) "Hwp".
  iApply wp_prim_ind_at_si_pure ; last done.
  { solve_proper. }
  iIntros (e1 Φ1 Σ') "#IH".
  iIntros (σ tid Htid) "#Hinv'".
  rewrite Ind_wp_unfold /=.
  destruct σ as [es h] ; simpl in Htid.
  destruct (to_val e1) as [v|] eqn:He1 ; simpl.
  - iPureIntro; exists e1, h; split ; [| by left].
    rewrite list_insert_id //.
  - iDestruct "IH" as (Σ'') "[#HΣ #IH]".
    rewrite excl_outEdges_injI.
    iAssert (▷ inv' (es, h) tid Σ'')%I as "Hinv''".
    { iNext; by iRewrite "HΣ". }
    iDestruct ("IH" with "Hinv''") as "[>%Hrb >IH']".
    destruct Hrb as [H1 | H1] ; last first.
    + destruct H1 as (l & Φ' & (k & e' & Hctx & He' & Hhb) & HΣ').
      inv Hhb; iPureIntro.
      exists (k (Recv #l)), h; split ; [rewrite list_insert_id // | ].
      right; exists k ; split ; eauto.
    + destruct H1 as (e' & h' & es_new & b & Hsteps).
      iDestruct ("IH'" with "[//]") as (Σ''') "[#HΣ'' IH''] /=".
      destruct b; simpl.
      * iPureIntro.
        exists e1, h; split ; [rewrite list_insert_id // |].
        right; rewrite concurrent_prim_step ; eauto.
      * rewrite aProp_at_and /=.
        iDestruct "IH''" as "[IH'' Hwp]".
        iDestruct "IH''" as (Σ2) "[#HΣ1 IH'']".
        iSpecialize ("IH''" $! (<[tid:=e']> es ++ es_new, h') tid).
        iAssert (▷ inv' (<[tid:=e']> es ++ es_new, h') tid Σ2)%I as "Hinv2".
        { rewrite excl_outEdges_injI; iNext. 
          iRewrite "HΣ1".
          rewrite -insert_app_l ; [| rewrite (list_lookup_alt es tid e1) in Htid ; by destruct Htid]. 
          iApply inv'_tid_irrelevant.
          by iApply inv'_ind_inv'. }
        assert ((<[tid:=e']> es ++ es_new) !! tid = Some e' ) as Htid'.
        { rewrite -insert_app_l ; [| rewrite (list_lookup_alt es tid e1) in Htid ; by destruct Htid].
          rewrite list_lookup_insert //.
          apply elem_of_list_split_length in Htid.
          destruct Htid as (l1 & l2 & -> & Hlen).
          rewrite !length_app /=; lia. }
        iDestruct ("IH''" with "[//] Hinv2") as ">%IH".
        iPureIntro.
        assert (es_new = []) as -> by (inv Hsteps ; by inv H0).
        rewrite app_nil_r in IH.
        destruct IH as (efin & hfin & Hsteps' & Hcond).
        rewrite list_insert_insert in Hsteps'.
        exists efin, hfin ; split ; [|done].
        assert (step (es, h) (<[tid:=e']> es ++ [], h')) as Hstep.
        { eexists _,_ ; econstructor ; eauto. }
        rewrite app_nil_r in Hstep.
        by eapply rtc_l.
Qed.

(* An invariant ensures that all threads are concurrently weakly normalizing *)
Lemma inv_locally_cwn σ :
  inv σ ⊢ ▷^2 ⌜ locally_cwn σ ⌝.
Proof.
  iIntros "#Hinv" (tid e Htid).
  rewrite (inv_unfold tid) //.
  iDestruct "Hinv" as (Σ) "[#Hinv #Hwp]".
  iPoseProof (wp_thread_cwn e _ _ with "Hwp") as "H".
  iNext. iSpecialize ("H" with "[//] Hinv").
  iMod "H".
  by iNext.
Qed.

Lemma adequacy_locally_cwn e σ : 
  (⊢ WP e {{ _, emp }}) →
  steps ([e],∅) σ →
  locally_cwn σ.
Proof.
  intros Hwp Hsteps.
  rewrite aProp_emp_valid inv_initialization in Hwp.
  assert (⊢ inv σ).
  { induction Hsteps as [σ|σ1 σ2 σ3 Hstep Hsteps IH]; [done|].
    apply IH, later_soundness. by rewrite -inv_preservation. }
  apply (pure_soundness (PROP:=siProp)), later_soundness, later_soundness. 
  by iApply inv_locally_cwn.
Qed.

Lemma adequacy_globally_cwn e σ : 
  (⊢ WP e {{ _, emp }}) →
  steps ([e],∅) σ →
  globally_cwn σ.
Proof.
  intros Hwp Hsteps.
  set (n := length σ.1).

  (* We'll build σ_k for k=0..n, with σ_0 = σ and after k steps the indices < k are "fixed". *)
  assert (Hbuild : ∀ k, k ≤ n → ∃ σk, steps σ σk ∧
                 (∀ i e, (i < k) → σk.1 !! i = Some e → is_Some (to_val e) ∨ concurrent e) ∧
                 length σk.1 = n ).
  { induction k as [|k IH]; intros Hle.
    - exists σ. split ; [done| ].
      split ; [intros ; lia | done].
    - destruct (IH ltac:(lia)) as (σk & Hsteps_to_σk & [Hfixed_k Hlen_σk]).
      assert (locally_cwn σk) as Hloc_σk.
      { eapply adequacy_locally_cwn ; [done|]; by etransitivity; [apply Hsteps|]. }
      assert (exists e, σk.1 !! k = Some e) as [ek Hlookupk].
      { eexists; apply list_lookup_lookup_total_lt; lia. }
      destruct (Hloc_σk k ek Hlookupk) as (e' & h' & Hsteps_one & He'_prop).
      exists ((<[k:= e']> σk.1, h')); split.
      + by etransitivity; [apply Hsteps_to_σk|].
      + split ; [| rewrite length_insert // ].
        intros i e1 Hlt Heqi.
        destruct (decide (i = k)) as [-> | Hneq].
        * rewrite list_lookup_insert in Heqi; [by inv Heqi| lia].
        * rewrite list_lookup_insert_ne in Heqi; [| congruence].
          eapply Hfixed_k ; [| done]; lia.
  }

  (* instantiate Hbuild with k = n *)
  destruct (Hbuild n ltac:(done)) as (σ' & Hsteps' & [Hall Hlen']).
  exists σ'; split; [done|].
  intros tid e1 Hlook.
  eapply Hall; [|done].
  apply elem_of_list_split_length in Hlook.
  destruct Hlook as (l1 & l2 & ? & Hlen). 
  assert (length σ'.1 = length (l1 ++ e1 :: l2)) as Hlen'' by rewrite H //. 
  rewrite length_app /= in Hlen''; lia.
Qed.

(* Definition of weak normalization for sequential steps.

   The present definition states that there exists a sequence of steps,
   not necessarily sequential. However, since we are seeking a concurrently
   reducible configuration, if we can take a concurrent step, then we have
   reached our goal. Hence, it does not change much if we restrict to
   sequential steps only.
*)
Definition wn_seq σ : Prop :=
  ∃ σ', steps σ σ' ∧ (final σ' ∨ creducible σ').

Lemma adequacy_live e σ :
  (⊢ WP e {{ _, emp }}) →
  steps ([e],∅) σ →
  wn_seq σ.
Proof.
  intros Hwp Hsteps.
  destruct (adequacy_globally_cwn e σ Hwp Hsteps) as (σ' & Hsteps' & Hprop).
  exists σ'; split ; [done|].
  assert (global_progress σ') as H.
  { eapply adequacy ; [done| by etransitivity ]. } 
  destruct H as [Hfinal | (σ'' & [b [i Hstep]])] ; [by left|].
  right; exists σ'', i; inv Hstep.
  destruct (Hprop i e1 H) as [Hv | Hc].
  - destruct (to_val e1) as [v|] eqn:He1; [| exfalso; by eapply is_Some_None ].
    rewrite to_val_Val in He1; subst.
    apply prim_step_not_val in H0; simpl in H0; congruence.
  - assert (prim_step e1 h1 e2 h2 es_new b) as Hprim by done.
    destruct Hc as (k & Hctx & [(l & [(v & ->)| ->]) | (f & ->)]).
    all: apply prim_step_ctx_inv in H0 ; [|done|done] ;
         destruct H0 as (e' & Hprim' & ->);
         inv_prim_step Hprim';
         by econstructor.
Qed.

(* Termination for single-threaded programs.

   We will prove strong normalization for programs that do not use concurrency
   features by defining a suitable inductive predicate, which we call sequential
   strong normalization.

   The main theorem of this section is that any sequence of sequential steps
   starting from an initial configuration ([e],∅) will eventually terminate.
   Hence, reaching a final configuration or a concurrently reducible
   configuration by the global progress theorem. As a corollary, if the program
   does not use concurrency features, then it will reach a final configuration.
*)

(* Sequential Strong normalization *)
Definition ssn_pre (ssn : cfg -d> siProp) : cfg -d> siProp :=
  λ σ1, (∀ tid σ2, ⌜ tsstep tid σ1 σ2 ⌝ → ◇ ssn σ2)%I.

Global Instance ssn_pre_ne : NonExpansive ssn_pre.
Proof. solve_proper. Qed.

Lemma ssn_pre_mono (ssn1 ssn2 : cfg -d> siProp) :
  □ (∀ σ, ssn1 σ -∗ ssn2 σ) -∗
  ∀ σ, ssn_pre ssn1 σ -∗ ssn_pre ssn2 σ.
Proof.
  iIntros "#H"; iIntros (σ) "Hwp". rewrite /ssn_pre.
  iIntros (tid σ2 Hstep).
  iSpecialize ("Hwp" with "[//]").
  iMod "Hwp". iModIntro.
  by iApply "H".
Qed.

Local Instance ssn_pre_mono' : BiMonoPred ssn_pre.
Proof.
  constructor; first (intros ????; apply ssn_pre_mono).
  intros wp Hwp n t1 t2 ?%(discrete_iff _ _)%leibniz_equiv; solve_proper.
Qed. 

Definition ssn (σ : cfg) : siProp := bi_least_fixpoint ssn_pre σ.

Lemma ssn_unfold σ : ssn σ ⊣⊢ ssn_pre ssn σ.
Proof. by rewrite /ssn least_fixpoint_unfold. Qed.

Global Instance ssn_is_except_0 σ : IsExcept0 (ssn σ).
Proof. 
  unfold IsExcept0. iIntros "H".
  rewrite ssn_unfold /ssn_pre.
  iIntros (tid σ2 Hstep).
  iMod "H".
  by iApply "H".
Qed.

Lemma ssn_ind Ψ :
  ⊢ (□ ∀ σ, ssn_pre (λ σ, Ψ σ ∧ ssn σ) σ -∗ Ψ σ) → ∀ σ, ssn σ -∗ Ψ σ.
Proof.
  iIntros "#IH" (σ) "H".
  assert (NonExpansive Ψ).
  { by intros n ?? ->%(discrete_iff _ _)%leibniz_equiv. }
  iApply (least_fixpoint_ind _ Ψ with "[] H").
  iIntros "!>" (es') "H". by iApply "IH".
Qed.

Program Definition is_empty (Φ1 : val -d> aProp) : outEdges -n> siProp 
  := λne Σ, (∀ v : val, aProp_at (Φ1 v) Σ → aProp_at ((λ _ : val, emp) v) Σ)%I.
Next Obligation. solve_proper. Qed.

Program Definition Ψssn1 Σ : expr → (val -d> aProp) -n> siProp := λ e,
  (λne (Φ : val -d> aProp),  
    (∀ e2 h1 h2, 
    ⌜ prim_step e h1 e2 h2 [] false ⌝ →
    ▷ (∀ Σ', is_empty Φ Σ') →
    ▷ inv' ([e], h1) 0 Σ → ssn (<[0:=e2]> [e], h2) ))%I.
Next Obligation. solve_proper. Qed.

(* Initialization Lemma *)
Lemma ssn_initialization_aux e Φ Σ :
  aProp_at (wp_prim e Φ) Σ ⊢ ▷ Ψssn1 Σ e Φ.
Proof.
  iIntros "Hwp". iRevert "Hwp".  iRevert (e Φ Σ).
  iApply wp_prim_ind_at_si_pure.
  { solve_proper. }
  iIntros (e1 Φ1 Σ ) "#IH".
  rewrite /Ψssn1 /=. iIntros (e2 h1 h2 Hprim) "#Hemp #Hinv".
  rewrite Ind_wp_unfold /=.
  assert (to_val e1 = None) as -> by (apply prim_step_not_val in Hprim; done) ; simpl.
  iDestruct "IH" as (Σ'') "[#HΣ #IH]".
  rewrite excl_outEdges_injI.
  iAssert (▷ inv' ([e1], h1) 0 Σ'')%I as "Hinv''".
  { iNext; by iRewrite "HΣ". }
  iSpecialize ("IH" with "Hinv''").
  iMod "IH".
  iDestruct "IH" as "[%Hrb IH']".
  destruct Hrb as [H1 | H1] ; last first.
  { destruct H1 as (e' & h' & Hblocked & Hchan).
    destruct Hblocked as (k & e'' & Hk & Heq & Hhead).
    inv Hhead.
    apply prim_step_false_not_concurrent in Hprim.
    exfalso. apply Hprim.
    exists k ; eauto. }
  destruct H1 as (e' & h' & es_new & b & Hsteps).
  iDestruct ("IH'" with "[//]") as (Σ''') "[#HΣ'' [IH'' Hwp]] /=".
  destruct (prim_step_deterministic _ _ _ _ _ _ _ _ _ _ Hsteps Hprim) as (-> & -> & -> & ->).
  clear Hsteps.  iClear "IH'".
  iDestruct "IH''" as (Σ2) "[#HΣ1 #IH]/=".
  rewrite excl_outEdges_injI.
  rewrite ssn_unfold /ssn_pre. iIntros (tid σ2 Hstep).
  inv Hstep.
  assert (tid = 0) as ->.
  { rewrite list_lookup_singleton in H1; destruct tid ; congruence. }
  assert (es_new = []) as ->.
  { by inv H5; inv H0. }
  rewrite right_id /=.
  assert (e2 = e0) as ->.
  { rewrite list_lookup_singleton in H1; congruence. }
  iAssert (▷ inv' ([e0], h2) 0 Σ2)%I as "HinvH".
  { iNext; iRewrite "HΣ1".
    replace ([e0]) with (<[0:=e0]> [e1]) by done.
    iApply inv'_tid_irrelevant; eauto.
    by iApply inv'_ind_inv'.
  }
  iModIntro. iApply "IH" ; eauto.
Qed.

Lemma ssn_initialization e :
  aProp_at (WP e {{ _, emp }}) ∅ ⊢ ▷ ssn ([e], ∅).
Proof.
  rewrite wp_wp_prim.
  iIntros "#Hwp".
  iPoseProof (ssn_initialization_aux e _ _ with "Hwp") as "H".
  rewrite /Ψssn1 /=.
  iNext.
  rewrite ssn_unfold /ssn_pre.
  iIntros (tid σ2 Hstep).
  inv Hstep.
  assert (tid = 0) as ->.
  { rewrite list_lookup_singleton in H1; destruct tid ; congruence. }
  assert (e = e1) as ->.
  { rewrite list_lookup_singleton in H1; congruence. }
  assert (es_new = []) as ->.
  { by inv H5; inv H0. }
  rewrite right_id /=.
  iModIntro.
  iApply "H" ; eauto.
  - by iIntros (Σ' v) "!> H2". 
  - iNext. 
   iExists ∅. iSplit; [iPureIntro; apply empty_wf|].
    iIntros (ν). rewrite out_edges_empty in_labels_empty /=.
    destruct ν as [[|i]|l]; simpl.
    + auto.
    + rewrite aProp_at_affinely aProp_at_pure. auto.
    + rewrite lookup_empty /= aProp_at_affinely aProp_at_pure. auto.
  Qed.

(* snn preservation under sequential steps *)
Lemma ssn_sstep σ1 σ2 :
  sstep σ1 σ2 →
  ssn σ1 ⊢ ssn σ2.
Proof.
  iIntros (Hstep) "Hssn".
  rewrite ssn_unfold /ssn_pre.
  
  assert (∃ tid, tsstep tid σ1 σ2) as (tid & Hstep').
  { destruct Hstep as [tid Hstep'] ; eauto. }
  iSpecialize ("Hssn" with "[//]").
  by iMod "Hssn".
Qed.

Lemma ssn_strong_normalization σ :
  ssn σ ⊢ ▷ ⌜ sn sstep σ ⌝.
Proof.
  iRevert (σ).
  iApply ssn_ind.
  iIntros "!>" (σ) "Hssn".
  iApply (bi.pure_mono _ _ (Acc_intro _)).
  iIntros (σ' Hstep).
  rewrite /ssn_pre.
  assert (∃ tid, tsstep tid σ σ') as (tid & Hstep').
  { destruct Hstep as [tid Hstep'] ; eauto. }
  iSpecialize ("Hssn" with "[//]").
  iMod "Hssn".
  iDestruct "Hssn" as "[$ _]".
Qed.

Lemma sequential_sn e σ :
  (⊢ WP e {{ _, emp }}) →
  rtc sstep ([e],∅) σ →
  sn sstep σ.
Proof.
  intros Hwp Hsteps.
  rewrite aProp_emp_valid ssn_initialization in Hwp.
  assert (⊢ ▷ ssn σ).
  { induction Hsteps as [σ|σ1 σ2 σ3 Hstep Hsteps IH]; [done|].
    apply IH. by rewrite -ssn_sstep. }
  apply (pure_soundness (PROP:=siProp)), later_soundness, later_soundness. 
  by iApply ssn_strong_normalization.
Qed.
