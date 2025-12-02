From dlfactris.lang Require Export lang.

(* Basic properties about contexts *)
Lemma ctx_compose k1 k2 :
  ctx k1 → ctx k2 → ctx (k1 ∘ k2).
Proof.
  intros Hk1 Hk2. induction Hk1 as [|k1 k1']; [done|].
  by apply (Ctx_compose k1).
Qed.

Global Instance ctx1_inj k : ctx1 k → Inj (=) (=) k.
Proof. intros Hk. induction Hk; intros ???; simplify_eq/=; auto with f_equal. Qed.

Global Instance ctx_inj k : ctx k → Inj (=) (=) k.
Proof.
  intros Hk; induction Hk; intros ???; simplify_eq/=; auto with f_equal.
  apply ctx1_inj in H; eauto.
Qed.

Lemma ctx1_no_val_inj k1 k2 e1 e2 :
  ctx1 k1 → ctx1 k2 →
  to_val e1 = None → to_val e2 = None →
  k1 e1 = k2 e2 → k1 = k2.
Proof.
  intros Hctx1 Hctx2.
  revert k1 Hctx1.
  induction Hctx2; intros k1 Hctx1; induction Hctx1; naive_solver eauto with f_equal.
Qed.

Lemma pure_step_not_val e1 e2 :
  pure_step e1 e2 → to_val e1 = None.
Proof. by intros []. Qed.

Lemma to_val_ctx_None k e :
  ctx k → to_val e = None → to_val (k e) = None.
Proof. intros Hctx. revert e. induction Hctx as [|?? []]; eauto. Qed.

Lemma head_step_not_val e1 h1 e2 h2 es_new b :
  head_step e1 h1 e2 h2 es_new b → to_val e1 = None.
Proof. intros []; eauto using pure_step_not_val. Qed.

Lemma prim_step_not_val e1 h1 e2 h2 es_new b :
  prim_step e1 h1 e2 h2 es_new b → to_val e1 = None.
Proof. intros []; eauto using to_val_ctx_None, head_step_not_val. Qed.

Lemma head_step_prim_step e1 h1 e2 h2 es_new b :
  head_step e1 h1 e2 h2 es_new b → prim_step e1 h1 e2 h2 es_new b.
Proof. intros. apply (Prim_step id); eauto using ctx. Qed.

Lemma head_step_reducible_or_blocked e1 h1 e2 h2 es_new b :
  head_step e1 h1 e2 h2 es_new b → reducible_or_blocked e1 h1.
Proof. left. eexists. eauto using head_step_prim_step. Qed.

Lemma pure_step_reducible_or_blocked e1 e2 h :
  pure_step e1 e2 → reducible_or_blocked e1 h.
Proof. eauto using head_step_reducible_or_blocked, head_step. Qed.

Lemma pure_step_no_ctx1 k e1 e2 :
  ctx1 k → pure_step (k e1) e2 → is_Some (to_val e1).
Proof. intros [] He1; inv He1; eauto. Qed.

Lemma to_val_ctx_is_Some_id k e :
  ctx k → is_Some (to_val (k e)) → k = id.
Proof. induction 1 as [|?? []]; intros [??]; naive_solver. Qed.

Lemma ctx_Val k e v :
  ctx k → k e = Val v → e = Val v.
Proof.
  intros ? Hke. assert (k = id) as ->; [|done].
  apply (to_val_ctx_is_Some_id _ e); by rewrite ?Hke.
Qed.

Lemma to_val_ctx_is_Some k e :
  ctx k → is_Some (to_val (k e)) → is_Some (to_val e).
Proof. intros. by assert (k = id) as -> by eauto using to_val_ctx_is_Some_id. Qed.

Lemma pure_step_no_ctx k e1 e2 :
  ctx k → pure_step (k e1) e2 → is_Some (to_val e1) ∨ k = id.
Proof. induction 1; eauto using to_val_ctx_is_Some, pure_step_no_ctx1. Qed.

Lemma pure_step_head_step e1 e2 e2' h h' es_new b :
  pure_step e1 e2 →
  head_step e1 h e2' h' es_new b →
  e2 = e2' ∧ h = h' ∧ es_new = [] ∧ b = false.
Proof.
  intros [] He2'; inv He2';
    match goal with H : pure_step _ _ |- _ => inv H end; auto.
Qed.

Lemma pure_step_prim_step e1 e2 e2' h h' es_new b :
  pure_step e1 e2 →
  prim_step e1 h e2' h' es_new b →
  e2 = e2' ∧ h = h' ∧ es_new = [] ∧ b = false.
Proof.
  intros Hpure Hprim; destruct Hprim as [k e1'' e2''].
  destruct (pure_step_no_ctx k e1'' e2) as [[]%not_eq_None_Some| ->];
    eauto using head_step_not_val, pure_step_head_step.
Qed.

Lemma prim_step_ctx k e1 h1 e2 h2 es_new b :
  ctx k →
  prim_step e1 h1 e2 h2 es_new b →
  prim_step (k e1) h1 (k e2) h2 es_new b.
Proof.
  intros Hctx Hprim. destruct Hprim as [k' e1' e2'].
  apply (Prim_step (k ∘ k')); eauto using ctx_compose.
Qed.

Lemma reducible_ctx k e h :
  ctx k → reducible e h → reducible (k e) h.
Proof.
  intros Hctx (e' & h' & es_new & ? & b).
  exists (k e'), h', es_new; eauto using prim_step_ctx.
Qed.

Lemma head_ctx1_step_val k e h1 e2 h2 es b :
  ctx1 k →
  head_step (k e) h1 e2 h2 es b → is_Some (to_val e).
Proof.
  intros Hctx Hstep.
  inv Hstep ; try (destruct Hctx ; by inv H0).
  apply pure_step_no_ctx1 in H; eauto.
Qed.

Lemma head_ctx_step_val k e1 h1 e2 h2 es b :
  ctx k →
  head_step (k e1) h1 e2 h2 es b → is_Some (to_val e1) ∨ k = id.
Proof. 
  induction 1; eauto using to_val_ctx_is_Some, head_ctx1_step_val.
Qed.

Lemma step_by_val k k' e1 e1' h1 e2 h2 es b :
  ctx k → ctx k' →
  k e1 = k' e1' →
  to_val e1 = None →
  head_step e1' h1 e2 h2 es b →
  ∃ k'', ctx k'' ∧ k' = k ∘ k''.
Proof. 
  intros Hk Hk' Heq Htv Hstep.
  revert k' Hk' Heq Htv.
  induction Hk ; eauto.
  intros k' Hk' Heq Htv.
  destruct Hk'.
  - simpl in Heq. subst e1'. apply head_ctx1_step_val in Hstep; auto.
    apply to_val_ctx_is_Some in Hstep ; eauto.
    apply not_eq_None_Some in Hstep ; congruence.
  - simpl in Heq.
    assert (k1 = k0) as ->.
    { eapply ctx1_no_val_inj, Heq ; eauto using to_val_ctx_None, head_step_not_val. }
    apply ctx1_inj in Heq ; eauto.
    destruct (IHHk k3 Hk' Heq Htv) as (K'' & HK'' & ->); auto.
    by exists K''. 
Qed.

Lemma base_redex_unique k k' e e' h :
  ctx k → ctx k' →
  k e = k' e' →
  head_reducible e h →
  head_reducible e' h →
  k = k' ∧ e = e'.
  Proof.
    intros Hk Hk' Heq (e2 & h2 & es & b & Hred) (e1' & h2' & es' & b' & Hred').
    edestruct (step_by_val k' k e' e) as (k'' & Hk'' & ->) ; eauto.
    { by eapply head_step_not_val. }
    simpl in Heq.
    apply ctx_inj in Heq ; eauto.
    subst.
    destruct (head_ctx_step_val _  _ _ _ _ _ _ Hk'' Hred') as [[]%not_eq_None_Some|HK''].
    { by apply head_step_not_val in Hred. }
    subst ; eauto.
  Qed.

Lemma blocked_ctx k e l h :
  ctx k → blocked e l h → blocked (k e) l h.
Proof.
  intros Hctx (k' & e' & ? & -> & ?).
  exists (k ∘ k'); eauto using ctx_compose.
Qed.

Lemma blocked_chan_unique h l l' k :
  ctx k →
  blocked (k (Recv (Val (LitV (LitLoc l))))) l' h → l = l'.
Proof.
  intros Hctx (k' & e' & Hctx' & Heq & Hbl). destruct Hbl as [_ l' _].
  revert k' Heq Hctx'. induction Hctx; induction 2;
    repeat match goal with
    | _ => progress simplify_eq/=
    | H : ctx1 _ |- _ => destruct H
    | Hk : ctx ?k, H : Val _ = ?k _ |- _ => symmetry in H; apply (ctx_Val _ _ _ Hk) in H
    | Hk : ctx ?k, H : ?k _ = Val _ |- _ => apply (ctx_Val _ _ _ Hk) in H
    end; eauto.
Qed.

Definition sub_exprs : expr → list expr :=
  fix go e :=
    e :: match e with
         | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Send e1 e2 | Store e1 e2 =>
           if decide (is_Some (to_val e2)) then go e1 ++ go e2 else go e2
         | UnOp _ e | If e _ _ | LetPair e _ | Sum _ e  | MatchSum e _
                    | ForkChan e | Recv e | Alloc e | Free e | Load e=> go e
         | _ => []
         end.

Lemma to_val_Val e v : to_val e = Some v ↔ e = Val v.
Proof. split; [|by intros ->]. destruct e; naive_solver. Qed.

Lemma sub_exprs_spec e' e : e' ∈ sub_exprs e ↔ ∃ k, ctx k ∧ e = k e'.
Proof.
  split.
  - revert e'. induction e; intros e' ?;
      repeat match goal with
      | _ => progress simplify_eq/=
      | _ => case_decide
      | H : _ ∈ [] |- _ => apply elem_of_nil in H as []
      | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H as []
      | H : _ ∈ _ ++ _ |- _ => apply elem_of_app in H as []
      | H : is_Some (to_val _) |- _ => destruct H as [v ->%to_val_Val]
      | H : _ ∈ _, IH : ∀ _, _ ∈ _ → _ |- _ => apply IH in H as (?&?&?)
      end; eauto 4 using ctx, ctx1.
  - intros (k&Hk&->). induction Hk as [|k1 k Hk1 Hk IH]; simpl.
    { destruct e'; set_solver. }
    destruct Hk1; simpl; repeat case_decide; set_solver.
Qed.

Lemma sub_exprs_self e : e ∈ sub_exprs e.
Proof. rewrite sub_exprs_spec; exists id; split; [apply Ctx_id|done]. Qed.

Lemma sub_exprs_ctx k e e' :
  ctx k → e' ∈ sub_exprs (e) → e' ∈ sub_exprs (k e).
Proof.
  intros Hctx Hsub.
  rewrite sub_exprs_spec in Hsub.
  rewrite sub_exprs_spec.
  destruct Hsub as (k'&Hk'&Heq).
  exists (k ∘ k'); split; [apply ctx_compose; auto|].
  by rewrite Heq.
Qed.

Global Instance head_blocked_dec e l h : Decision (head_blocked e l h).
Proof.
  refine
    match e with
    | Recv (Val (LitV (LitLoc l'))) =>
       cast_if_and (decide (l = l')) (decide (h !! l = Some (ChanHV None)))
    | _ => right _
    end; try first [inversion 1; naive_solver|by subst; constructor].
Defined.
Local Lemma blocked_alt e l h :
  blocked e l h ↔ Exists (λ e', head_blocked e' l h) (sub_exprs e).
Proof.
  rewrite /blocked Exists_exists. setoid_rewrite sub_exprs_spec. naive_solver.
Qed.
Global Instance blocked_dec e l h : Decision (blocked e l h).
Proof.
  refine (cast_if (decide (Exists (λ e', head_blocked e' l h) (sub_exprs e))));
    by rewrite blocked_alt.
Defined.

Lemma reducible_or_blocked_ctx k e h :
  ctx k → reducible_or_blocked e h → reducible_or_blocked (k e) h.
Proof.
  intros ? [? | [l ?]]; [left|right]; eauto using reducible_ctx, blocked_ctx.
Qed.

Ltac inv_prim_step Hps :=
  inversion Hps as [??????? []];
  repeat match goal with
    | Hk : ctx ?k, H : ?k _ = Val _ |- _ => apply (ctx_Val _ _ _ Hk) in H
    | _ => progress simplify_eq/=
    | H : head_step ?e _ _ _ _ _ |- _ => assert_fails (is_var e); inv H
    | H : pure_step ?e _ |- _ => assert_fails (is_var e); inv H
    | H : ctx1 _ |- _ => destruct H
    end.

Ltac inv_pure_ctx_step Hps :=
  inversion Hps as [? ? ? ? ?];
  repeat match goal with
    | Hk : ctx ?k, H : ?k _ = Val _ |- _ => apply (ctx_Val _ _ _ Hk) in H
    | _ => progress simplify_eq/=
    (* | H : head_step ?e _ _ _ _ _ |- _ => assert_fails (is_var e); inv H *)
    (* | H : pure_step ?e _ |- _ => assert_fails (is_var e); inv H *)
    | H : ctx1 _ |- _ => destruct H
  end.

Lemma prim_step_ctx1_inv k e h ke' h' es_new b :
  to_val e = None →
  ctx1 k →
  prim_step (k e) h ke' h' es_new b →
  ∃ e', prim_step e h e' h' es_new b ∧ ke' = k e'.
Proof. intros ?? Hps; inv_prim_step Hps; eauto using prim_step. Qed.

Lemma prim_step_ctx_inv k e h e' h' es_new b :
  to_val e = None →
  ctx k → prim_step (k e) h e' h' es_new b →
  ∃ e'', prim_step e h e'' h' es_new b ∧ e' = k e''.
Proof.
  intros Htv Hctx. revert e e' h h' Htv.
  induction Hctx as [|k k' ?? IH]; intros e e' h h' Htv Hps; [by eauto|].
  eapply (prim_step_ctx1_inv k) in Hps
    as (e'' & Hps & ->); naive_solver eauto using to_val_ctx_None.
Qed.

Lemma fork_reducible_or_blocked f h :
  reducible_or_blocked (ForkChan (Val f)) h.
Proof.
  eapply head_step_reducible_or_blocked with _ (<[fresh (dom h):=ChanHV None]> h) [_] _.
  econstructor.
  (* apply not_elem_of_dom, is_fresh. *)
Qed.

Lemma reducible_step i e σ :
  σ.1 !! i = Some e →
  reducible e σ.2 →
  ∃ σ', step σ σ'.
Proof.
  destruct σ as [es h]; simpl. intros ? (e'&h'&es'&?&?).
  eexists _, x. eauto using stepB.
Qed.

Lemma step_length σ σ' :
  step σ σ' →
  length σ.1 ≤ length σ'.1.
Proof.
  intros Hstep.
  destruct σ as [es h], σ' as [es' h'].
  destruct Hstep as [? [? []]].
  simplify_eq/=.
  rewrite length_app.
  rewrite length_insert.
  lia.
Qed.

Lemma steps_length σ σ' :
  steps σ σ' →
  length σ.1 ≤ length σ'.1.
Proof.
  intros Hsteps.
  induction Hsteps as [|σ1 σ2 σ3 Hstep Hsteps IH].
  - lia.
  - by etransitivity ; [eapply step_length | eapply IH].
Qed.

Fixpoint subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  destruct e; simpl; f_equal; simplify_option_eq; auto.
  select (list _) (fun tes => induction tes as [|[]]);
    simplify_eq/=; f_equal; auto with f_equal.
Qed.
Fixpoint subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. destruct e; simpl; try (by f_equal; auto).
  - simplify_option_eq; auto with f_equal.
  - f_equal. simplify_option_eq; auto with f_equal.
  - select (list _) (fun tes => induction tes as [|[]]);
      simplify_eq/=; f_equal; auto with f_equal.
Qed.

(* Parallel substitution *)
Fixpoint subst_map (vs : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | LetPair e1 e2 => LetPair (subst_map vs e1) (subst_map vs e2)
  | Sum t e => Sum t (subst_map vs e)
  | MatchSum e tes =>
      MatchSum
        (subst_map vs e)
        (prod_map id (subst_map vs) <$> tes)
  | ForkChan e => ForkChan (subst_map vs e)
  | Send e1 e2 => Send (subst_map vs e1) (subst_map vs e2)
  | Recv e => Recv (subst_map vs e)
  | Alloc e => Alloc (subst_map vs e)
  | Free e => Free (subst_map vs e)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  end.

Fixpoint subst_map_empty e : subst_map ∅ e = e.
Proof.
  destruct e; simplify_map_eq; rewrite ?binder_delete_empty; f_equal; auto.
  select (list _) (fun tes => induction tes as [|[]]);
    simplify_eq/=; repeat f_equal; auto.
Qed.
Fixpoint subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. destruct e=> vs; simplify_map_eq; try f_equal; auto.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end. by case (vs !! _); simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !binder_delete_insert // !binder_delete_delete; eauto with f_equal.
    + by rewrite /= delete_insert_delete delete_idemp.
    + by rewrite /= binder_delete_insert // delete_insert_delete
        !binder_delete_delete delete_idemp.
  - select (list _) (fun tes => induction tes as [|[]]);
      simplify_eq/=; f_equal; auto with f_equal.
Qed.

Lemma subst_map_binder_insert b v vs e :
  subst_map (binder_insert b v vs) e =
  subst' b v (subst_map (binder_delete b vs) e).
Proof. destruct b; rewrite ?subst_map_insert //. Qed.

Lemma subst_map_binder_insert_2 b1 v1 b2 v2 vs e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
  subst' b2 v2 (subst' b1 v1 (subst_map (binder_delete b2 (binder_delete b1 vs)) e)).
Proof.
  destruct b1 as [|s1], b2 as [|s2]=> /=; auto using subst_map_insert.
  rewrite subst_map_insert. destruct (decide (s1 = s2)) as [->|].
  - by rewrite delete_idemp subst_subst delete_insert_delete.
  - by rewrite delete_insert_ne // subst_map_insert subst_subst_ne.
Qed.


Lemma pure_step_pure_ctx_step e1 e2 : pure_step e1 e2 → pure_ctx_step e1 e2.
Proof. intros. apply (PureCtx_step id); auto using ctx. Qed.

Lemma pure_ctx_step_not_val e1 e2 :
  pure_ctx_step e1 e2 → to_val e1 = None.
Proof.
  intros [k e1' e2' Hk Hstep]. eauto using to_val_ctx_None, pure_step_not_val.
Qed.

Lemma pure_ctx_step_prim_step e1 e2 e2' h h' es_new b :
  pure_ctx_step e1 e2 →
  prim_step e1 h e2' h' es_new b →
  e2 = e2' ∧ h = h' ∧ es_new = [] ∧ b = false.
Proof.
  intros [k e1'' e2'' Hk Hpure] Hprim.
  destruct (prim_step_ctx_inv k e1'' h e2' h' es_new b) as (e2'''&?&->);
    [by eauto using pure_step_not_val..|].
  destruct (pure_step_prim_step e1'' e2'' e2''' h h' es_new b); naive_solver.
Qed.

Definition concurrent_sub e : Prop :=
  (∃ l, (∃ v, Send (Val (LitV (LitLoc l))) (Val v) ∈ sub_exprs e) ∨
       (Recv (Val (LitV (LitLoc l))) ∈ sub_exprs e)) ∨
  (∃ f, ForkChan (Val f) ∈ sub_exprs e).

Definition concurrent e : Prop :=
  ∃ k, ctx k ∧ ( (∃ l, (∃ v, e = k (Send (Val (LitV (LitLoc l))) (Val v))) ∨
                     (e = k (Recv (Val (LitV (LitLoc l)))))) ∨
                     (∃ f, e = k (ForkChan (Val f)))).

Lemma concurrent_prim_step e :
  concurrent e ↔ ∃ h e' h' es_new, prim_step e h e' h' es_new true.
Proof.
  split.
  - intros [k [Hk [ [l [(v2 & ->) | ->]] | (f & ->)] ]].
    + eexists (<[ l:=ChanHV None]> ∅), _, _, _.
      apply Prim_step; [done|];
      apply Send_step; rewrite lookup_insert //.
    + eexists (<[ l:=ChanHV (Some (LitV (LitInt 1)))]> ∅), _, _, _. (* you can pick any value*)
      apply Prim_step; [done|].
      apply Recv_step; rewrite lookup_insert //.
    + eexists ∅,  (k (Val (LitV (LitLoc xH)))), _, _ . (* xH is a fresh location *)
      apply Prim_step; [done|].
      eapply Fork_step.
      (* rewrite lookup_empty //. *)
  - intros (Hh & e2 & h' & es_new & Hprim).
    inversion Hprim ; subst.
    inv H0 ; exists k ; split ; eauto.
Qed.

Lemma concurrent_spec e :
  concurrent e ↔ concurrent_sub e.
Proof.
  split.
  - intros [k [Hk [ [l [(v2 & ->) | ->]] | (f & ->)] ]].
    + left; exists l; left; exists v2.
      apply sub_exprs_spec; eauto.
    + left; exists l; right.
      apply sub_exprs_spec; eauto.
    + right; exists f; apply sub_exprs_spec; eauto.
  - intros [ [l [(v2 & H) | H]] | (f & H)] ;
    rewrite sub_exprs_spec in H ;
    destruct H as (k & Hk & ->); exists k ;
    (split ; [done| eauto]).
Qed.


(* Alternative definition using a list of expressions *)
(* This is not used in the current code but can be useful for other purposes. *)

Fixpoint concurrentb_list (l : list expr) : bool :=
  match l with
  | Send (Val (LitV (LitLoc _))) (Val _) :: _ => true
  | Recv (Val (LitV (LitLoc _))) :: _ => true
  | (ForkChan (Val _) :: _) => true
  | _ :: l' => concurrentb_list l'
  | [] => false
  end.

Definition concurrentb e : bool := concurrentb_list (sub_exprs e).

Lemma concurrent_sub_spec e :
  concurrent_sub e ↔ concurrentb e = true.
Proof.
  split.
  - rewrite /concurrentb /concurrent_sub.
    induction (sub_exprs e) .
    + intros [ [l [ (v2 & H) | H]] | (f & H)] ; rewrite elem_of_nil // in H.
    + intros [ [l' [ (v2 & H) | H]] | (f & H)]  ; rewrite elem_of_cons in H.
      * simpl in H.
        destruct H as [H | H] ; [rewrite -H // |].
        assert (concurrentb_list l = true) by (apply IHl; eauto).
        rewrite /= H0.
        destruct a ; try done.
        -- destruct a ; try done.
        -- destruct a1, a2; try done ;
           destruct v ; try done ; destruct l0 ; done.
        -- destruct a ; try done.
           destruct v ; try done ; destruct l0 ; done.
      * simpl in H.
        destruct H as [H | H] ; [rewrite -H // |].
        assert (concurrentb_list l = true) by (apply IHl; eauto).
        rewrite /= H0.
        destruct a; try done.
        -- destruct a; done.
        -- destruct a1, a2; try done ;
           destruct v ; try done ; destruct l0 ; done.
        -- destruct a; try done.
           destruct v ; try done ; destruct l0 ; done.
      * simpl in H.
        destruct H as [H | H] ; [rewrite -H // |].
        assert (concurrentb_list l = true) by (apply IHl; eauto).
        rewrite /= H0.
        destruct a; try done.
        -- destruct a; done.
        -- destruct a1, a2; try done ;
           destruct v ; try done ; destruct l0 ; done.
        -- destruct a; try done.
           destruct v ; try done ; destruct l0 ; done.
  - intros H.
    rewrite /concurrentb /= in H.
    rewrite /concurrent_sub.
    induction (sub_exprs e) as [|a lsub IH] ; [done|].
    setoid_rewrite elem_of_cons.
    simpl in H.
    destruct a; try (destruct (IH H) as [[l [(v2 & H') | H']] | (f' & H')] ; eauto 6).
    + destruct a ; try (destruct (IH H) as [[l' [(v2 & H') | H']] | (f' & H') ] ; eauto 6).
      eauto.
    + destruct a1 ; try (destruct (IH H) as [ [l' [(v2 & H') | H']] | (f' & H')] ; eauto 6).
      destruct v ; try (destruct (IH H) as [ [l' [(? & H') | H'] ] (f' & H')] ; eauto 6).
      * destruct l; try (destruct (IH H) as [ [l' [(v2 & H') | H'] ] | (f' & H')] ; eauto 6).
         destruct a2 ; try (destruct (IH H) as [ [l' [(v2 & H') | H'] ] | (f' & H')] ; eauto 6).
         eauto 6.
      * destruct (IH H) as [ [l' [(? & H') | H'] ] | (f' & H')] ; eauto 6.
      * destruct (IH H) as [ [l' [(? & H') | H'] ] | (f' & H')] ; eauto 6.
      * destruct (IH H) as [ [l' [(? & H') | H'] ] | (f' & H')] ; eauto 6.
    + destruct a ; try (destruct (IH H) as [[l' [(v2 & H') | H']] | (f' & H') ] ; eauto 6).
      destruct v ; try (destruct (IH H) as [ [l' [(? & H') | H'] ] (f' & H')] ; eauto 6).
      * destruct l; try (destruct (IH H) as [ [l' [(v2 & H') | H'] ] | (f' & H')] ; eauto 6) ; eauto .
      * destruct (IH H) as [ [l' [(? & H') | H'] ] | (f' & H')] ; eauto 6.
      * destruct (IH H) as [ [l' [(? & H') | H'] ] | (f' & H')] ; eauto 6.
      * destruct (IH H) as [ [l' [(? & H') | H'] ] | (f' & H')] ; eauto 6.
Qed.

Lemma concurrent_sub_spec_false e :
  ¬ concurrent_sub e → concurrentb e = false.
Proof.
  intros Hnc.
  assert (concurrentb e = false ↔ ¬ (concurrentb e = true)) as ->.
  { split ; intros ;
    destruct (concurrentb e) eqn:Hc ; congruence.
  }
  rewrite concurrent_sub_spec // in Hnc.
Qed.

Global Instance decision_iff  P Q :
  Decision P → (P ↔ Q) → Decision Q.
Proof.
  intros [Hp | Hnp] [H1 H2].
  - left. apply H1. exact Hp.
  - right. intro Hq. apply Hnp. apply H2. exact Hq.
Qed.

Global Instance concurrent_dec e :
  Decision (concurrent e).
Proof.
  eapply decision_iff ; last first.
  - transitivity (concurrent_sub e) ; last first .
    + symmetry. apply concurrent_spec.
    + symmetry. apply concurrent_sub_spec.
  - solve_decision.
Qed.

Lemma concurrent_Ctx k e :
  ctx k →  concurrent e → concurrent (k e).
Proof.
  intros Hk Hstp.
  rewrite concurrent_spec /concurrent_sub  in Hstp.
  rewrite concurrent_spec /concurrent_sub .
  destruct Hstp as [ [l [(v' & Hstp) | Hstp]] | (f & Hstp)] .
  - left. exists l; left; exists v'.
    by apply sub_exprs_ctx with (k := k) in Hstp.
  - left. exists l. right. by apply sub_exprs_ctx with (k := k) in Hstp.
  - right. exists f.
    by apply sub_exprs_ctx with (k := k) in Hstp.
Qed.
    
Lemma concurrent_not_Ctx k e :
  ctx k →  ¬ concurrent (k e) → ¬ concurrent e.
Proof.
  intros Hk Hsrn Hsr.
  apply Hsrn. by apply concurrent_Ctx.
Qed.

Lemma concurrent_not_Ctx_inv k e :
  to_val e = None →
  ctx k →  ¬ concurrent e → ¬ concurrent (k e).
Proof.
  intros Hv Hk Hsrn Hsr.
  rewrite concurrent_prim_step in Hsr.
  destruct Hsr as (h & e2' & h' & es & Hprim).
  apply prim_step_ctx_inv in Hprim ; eauto.
  destruct Hprim as (e2'' & Hprim' & Heq).
  rewrite concurrent_prim_step in Hsrn.
  apply Hsrn. eauto.
Qed.

Lemma concurrent_not_pure_step e1 e2 :
  pure_step e1 e2 →
  ¬ concurrent e1.
Proof.
  rewrite concurrent_spec.
  intros Hstep [[l [(v2 & Hsr) | Hsr]] | (f & Hsr)]; inv Hstep ; set_solver.
Qed.

Lemma concurrent_head_step e1 h e2 h' es_new b :
  head_step e1 h e2 h' es_new b → concurrentb e1 = b.
Proof.
  intros Hstep; inv Hstep ; (try (rewrite /concurrentb //)).
  set H' := (concurrent_sub_spec_false).
  unfold concurrentb in H'.
  apply H'.
  rewrite -concurrent_spec.
  by eapply concurrent_not_pure_step. 
Qed.

Lemma concurrent_not_pure_ctx_step e1 e2 :
  pure_ctx_step e1 e2 →
  ¬ concurrent e1.
Proof.
  intros Hstep Hsr.
  rewrite concurrent_prim_step in Hsr.
  destruct Hsr as (h & e2' & h' & es & Hprim).
  destruct (pure_ctx_step_prim_step _ _ _ _ _ _ _ Hstep Hprim) as (_ & _ & _ & ?).
  congruence.
Qed.

Lemma prim_step_false_not_concurrent e h e' h' es_new :
  prim_step e h e' h' es_new false →
  ¬ concurrent e.
Proof.
  intros Hstep Hconcur.
  rewrite concurrent_prim_step in Hconcur.
  destruct Hconcur as (hc & ec & hc' & es_newc & Hstepc).
  inv Hstep.
  inv Hstepc.
  assert (∃ k', ctx k' ∧ k0 = k ∘ k') as (kk & Hkk & ->).
  { eapply (step_by_val k k0) ; eauto.
    by eapply head_step_not_val. }
  simpl in H1.
  apply ctx_inj in H1 ; auto.
  subst.
  assert ( head_step (kk e0) h e2 h' es_new false) as H4 by done.
  apply head_ctx_step_val in H4 ; eauto.
  destruct H4 as [[v Hval] | ->]; [inv H3|].
  simpl in H0.
  inv H0 ; inv H3 ; inv H ; inv H1.
Qed.

Class deterministic {A} (R : relation A) := 
  deterministic_def : ∀ x y1 y2, R x y1 → R x y2 → y1 = y2.

Class sub_relation {A} (R1 R2 : relation A) := 
  sub_relation_def : ∀ x y, R1 x y → R2 x y.

Global Instance sub_relation_refl {A} (R : relation A) : sub_relation R R.
Proof. intros x ; eauto. Qed.

Global Instance sub_relation_trans {A} (R1 R2 R3 : relation A)
  `{!sub_relation R1 R2} `{!sub_relation R2 R3} : sub_relation R1 R3.
Proof. intros x; eauto. Qed.

Global Instance sub_relation_nsteps {A} (R1 R2 : relation A) {n}
  `{!sub_relation R1 R2} : sub_relation (nsteps R1 n) (nsteps R2 n).
Proof.
  induction n ; intros x y Hnsteps.
  - inv Hnsteps. by apply nsteps_O.
  - inv Hnsteps.
    econstructor.
    + by eapply sub_relation_def.
    + by eapply IHn.
Qed.

Global Instance sub_relation_rtc {A} (R1 R2 : relation A)
  `{!sub_relation R1 R2} : sub_relation (rtc R1) (rtc R2).
Proof.
  intros x y Hrtc.
  apply rtc_nsteps in Hrtc.
  apply rtc_nsteps.
  destruct Hrtc as (n & Hnsteps).
  exists n.
  by eapply sub_relation_nsteps.
Qed.

Global Instance sub_relation_rtc_inv {A} (R : relation A) : sub_relation R (rtc R).
Proof.
  intros x y Hrtc.
  by eapply rtc_once.
Qed.

Global Instance sub_relation_nsteps_rtc {A} {n} (R : relation A) : sub_relation (nsteps R n) (rtc R).
Proof.
  intros x y Hrtc.
  eapply rtc_nsteps.
  exists n; eauto.
Qed.

Global Instance sub_relation_deterministic {A} (R1 R2 : relation A)
  `{!sub_relation R1 R2} `{!deterministic R2} : deterministic R1.
Proof.
  intros x y1 y2 H1 H2.
  eapply deterministic_def; eauto.
Qed.

Global Instance deterministic_nsteps {A} (R : relation A) `{!deterministic R} n : deterministic (nsteps R n).
Proof.
  induction n ; intros x y z H1 H2.
  - by inv H1 ; inv H2.
  - inv H1 ; inv H2.
    assert (y0 = y1) as -> by eauto.
    eapply IHn ; eauto.
Qed.

Lemma nsteps_mid {A} {R : relation A} m n x z :
  nsteps R n x z →
  m ≤ n →
  ∃ y, nsteps R m x y ∧ nsteps R (n - m) y z.
Proof.
  revert x z m.
  induction n ; intros x z m Hnsteps Hle.
  - inv Hnsteps.
    replace m with 0 in * by lia.
    replace (0 - 0) with 0 in * by lia.
    exists z; split ; [apply nsteps_O | apply nsteps_O].
  - destruct m.
    + replace (S n - 0) with (S n) by lia.
      exists x; split ; [apply nsteps_O | done].
    + replace (S n) with (1 + n) in * by lia.
      destruct (decide (S m = 1 + n)) as [-> | Hneq].
      * replace (1 + n - (1 + n)) with 0 by lia.
        by exists z; split ; [| apply nsteps_O].
      * apply nsteps_add_inv in Hnsteps as (y' & Hstep & Hnsteps1).
        destruct (IHn _ _ m Hnsteps1 ltac:(lia)) as (y & Hnsteps_m & Hnsteps_rest).
        exists y ; split.
        -- replace (S m) with (1 + m) by lia.
           by eapply nsteps_trans.
        -- by replace (1 + n - S m) with (n - m) by lia.
Qed.


Lemma deterministic_wn_sn {A : Type} {R : relation A} `{!deterministic R} (x : A) :
  wn R x → sn R x.
Proof.
  intros (y & Hpath & Hnf).
  apply rtc_nsteps in Hpath.
  destruct Hpath as (n & Hpath).
  revert x Hpath.
  induction n ; intros x Hpath.
  - inv Hpath. by apply nf_sn.
  - replace (S n) with (1 + n) in Hpath by lia.
    apply nsteps_add_inv in Hpath as (y' & Hnsteps & Hstep).
    specialize (IHn y' Hstep).
    econstructor. intros y'' Hnsteps'.
    apply nsteps_once_inv in Hnsteps.
    by assert (y' = y'') as -> by (by eapply deterministic_def).
Qed.

Global Instance pure_step_deterministic : deterministic pure_step.
Proof.
  intros e1 e2 e3 Hstep1 Hstep2 ; inv Hstep1 ; inv Hstep2 ; eauto.
Qed.

Global Instance pure_ctx_step_deterministic : deterministic pure_ctx_step.
Proof.
  intros e1 e2 e3 Hstep1 Hstep2 ; inv Hstep1 ; inv Hstep2. 
  assert (k0 = k ∧ e1 = e0) as  (-> & ->).
  { eapply base_redex_unique; eauto ; eexists _, _,_,_ ; econstructor ; eauto. }
  by assert (e4 = e2) as -> by (eapply deterministic_def ; eauto).
  Unshelve. exact ∅.
Qed.
Ltac inv_head_step Hps :=
  inv Hps ;
  repeat match goal with
    | _ => progress simplify_eq/=
    | H : head_step ?e _ _ _ _ _ |- _ => assert_fails (is_var e); inv H
    | H : pure_step ?e _ |- _ => assert_fails (is_var e); inv H
    end.

Lemma head_step_deterministic e1 h1 e2 h2 es b e2' h2' es' b' :
  head_step e1 h1 e2 h2 es b →
  head_step e1 h1 e2' h2' es' b' →
  e2 = e2' ∧ h2 = h2' ∧ es = es' ∧ b = b'.
Proof.
  intros H1 H2. inv_head_step H1 ; eauto.
  inv_head_step H2. repeat split.
  eapply pure_step_deterministic ; eauto.
Qed.

Lemma prim_step_deterministic e1 h1 e2 h2 es b e2' h2' es' b' :
  prim_step e1 h1 e2 h2 es b →
  prim_step e1 h1 e2' h2' es' b' →
  e2 = e2' ∧ h2 = h2' ∧ es = es' ∧ b = b'.
Proof.
  intros H1 H2. inv H1 ; inv H2.
  edestruct (base_redex_unique k0 k e1 e0 h1 H3 H H1) as (-> & ->) ; [eexists ; eauto..|].
  by destruct (head_step_deterministic _ _ _ _ _ _ _ _ _ _ H0 H4) as (-> & -> & -> & ->).
Qed.

Global Instance tsstep_tstep_sub_relation tid :
  sub_relation (tsstep tid) (tstep tid).
Proof.
  intros σ1 σ2 Hstep.
  inv Hstep. econstructor ; econstructor ; eauto.
Qed.

Global Instance tstep_step_sub_relation tid :
  sub_relation (tstep tid) step.
Proof.
  intros σ1 σ2 Hstep.
  inv Hstep. econstructor ; econstructor ; eauto.
Qed.

Global Instance tstep_deterministic tid : deterministic (tstep tid).
Proof.
  intros [es h] [es1 h1] [es2 h2] [? Hstep1] [? Hstep2].
  inv Hstep1 ; inv Hstep2.
  simplify_eq/=.
  by destruct (prim_step_deterministic e1 h e2 h1 _ _ _ h2 _ _ H6 H8) as (-> & -> & -> & _).
Qed.
