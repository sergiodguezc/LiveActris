(**
  This file contains the computation of fixpoints for recursive predicates
  whose negative ocurrences are guarded by the later modality, as in the
  case of the Banach fixpoint theorem, and the positive ocurrences are
  monotonic, as in the case of the Knaster-Tarski theorem.

   Example: Find a predicate P : A → PROP such that P x ≡ ▷ P x → P x
*)
From iris.si_logic Require Export siprop.
From iris.algebra Require Export ofe.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From iris.bi.lib Require Import fixpoint_mono.
Import bi.

(* Computation of fixpoints *)

Program Definition lfix {A : ofe} {PROP : bi}
  (F : (A -d> PROP) → (A -d> PROP) → A -d> PROP)
  (Φ : A -n> PROP) : A -n> PROP := λne a, bi_least_fixpoint (F Φ) a.
Next Obligation.
  solve_proper_prepare.
  apply least_fixpoint_ne ; [|done].
  solve_proper.
Qed.

Local Definition least_banach_fixpoint_def {A : ofe} {PROP : bi}
  (F : (A -d> PROP) → (A -d> PROP) → A -d> PROP)
  `{!Contractive (lfix F)} : A -d> PROP := fixpoint (lfix F).

Local Definition least_banach_fixpoint_aux : seal (@least_banach_fixpoint_def). Proof. by eexists. Qed.
Definition least_banach_fixpoint := least_banach_fixpoint_aux.(unseal).
Global Arguments least_banach_fixpoint {_ _} F {_}.
Local Definition least_banach_fixpoint_unseal :
  @least_banach_fixpoint = @least_banach_fixpoint_def := least_banach_fixpoint_aux.(seal_eq).

Section least_banach_fixpoint.
  Context {A : ofe} {PROP : bi}.
  Context {F : (A -d> PROP) → (A -d> PROP) → A -d> PROP}.
  Context {F_mono : ∀ Φ : A -n> PROP, BiMonoPred (F Φ)}.
  Context {F_contractive : ∀ n, Proper (dist_later n ==> dist n ==> dist n) F}.

  Local Instance F_proper : Proper ((≡) ==> (≡) ==> (≡)) F.
  Proof using F_contractive.
    solve_proper_prepare.
    apply equiv_dist ; intros n.
    apply F_contractive.
    - rewrite equiv_dist in H.
      rewrite dist_later_fin_iff.
      destruct n ; [done| apply H ; lia ].
    - rewrite equiv_dist in H0.
      apply H0.
  Qed.

  Global Instance lfix_contractive : Contractive (lfix F).
  Proof using F_contractive.
    solve_proper_prepare.
    apply least_fixpoint_ne ; [|done].
    solve_proper_prepare. apply F_contractive ; [ | done].
    rewrite dist_later_fin_iff in H.
    by rewrite dist_later_fin_iff.
  Qed.

  Global Instance least_banach_fixpoint_ne : NonExpansive (least_banach_fixpoint F).
  Proof.
    rewrite least_banach_fixpoint_unseal /least_banach_fixpoint_def.
    solve_proper.
  Qed.

  Local Notation fixF := (least_banach_fixpoint F).

  Lemma least_banach_fixpoint_unfold : fixF ≡ F fixF fixF.
  Proof using F_mono.
    rewrite {1}least_banach_fixpoint_unseal /least_banach_fixpoint_def.
    etransitivity.
    - apply (fixpoint_unfold (lfix F)). 
    - rewrite {1}/lfix. intros a.
      rewrite /= least_fixpoint_unfold.
      apply F_proper.
      + rewrite least_banach_fixpoint_unseal /least_banach_fixpoint_def //. 
      + symmetry. 
        intros b.  
        rewrite least_banach_fixpoint_unseal /least_banach_fixpoint_def.
        etransitivity.
        * apply (fixpoint_unfold (lfix F)).
        * rewrite {1}/lfix //.
  Qed.

  Lemma least_banach_fixpoint_ind (Φ : A -n> PROP) `{NonExpansive fixF} :
    □ (∀ y, F fixF (λ x, Φ x ∧ fixF x) y -∗ Φ y) -∗
    ∀ x, fixF x -∗ Φ x.
  Proof using F_mono.
    iIntros  "IH" (x) "HfixF".
    iApply (least_fixpoint_ind (F fixF) with "[IH]") ; last first.
    - rewrite least_banach_fixpoint_unseal /least_banach_fixpoint_def.
      rewrite (fixpoint_unfold (lfix F) _).
      by rewrite {1}/lfix /=.
    - iApply intuitionistically_intro' ; [| iApply "IH"].
      iIntros "IH" (y) "HΨ".
      iApply "IH".
      unshelve epose (H1 := F_proper fixF fixF (ltac:(reflexivity)) (λ x0 : A, bi_and (Φ x0) (bi_least_fixpoint (F fixF) x0)) (λ x0 : A, bi_and (Φ x0) (fixF x0)) _ ).
      + intros z.
        rewrite least_banach_fixpoint_unseal /least_banach_fixpoint_def.
        rewrite (fixpoint_unfold (lfix F) _).
        rewrite {1}/lfix /= ; auto.
      + by rewrite (H1 _).
    Unshelve. 
    unshelve epose (fixFne := {| ofe_mor_car := fixF ; ofe_mor_ne := NonExpansive0 |}).
    apply (F_mono fixFne).
  Qed.

End least_banach_fixpoint.

Module example1.
  Parameter A : ofe.
  Definition F (Φ φ : A -d> siProp) : A -d> siProp := λ a, (▷ (Φ a) → φ a )%I.

  Instance F_contractive n : Proper (dist_later n ==> dist n ==> dist n) F.
  Proof.
    intros φ1 φ2 Hφ x y Hxy a. rewrite /F /=.
    apply impl_ne ; [| apply Hxy ].
    apply later_contractive.
    rewrite dist_later_fin_iff.
    destruct n ; [done| apply Hφ ; lia ].
  Qed.

  Instance F_proper : Proper ((≡) ==> (≡) ==> (≡)) F.
  Proof. solve_proper. Qed.

  Instance F_mono : ∀ Φ : A -n> siProp, BiMonoPred (F Φ).
  Proof.
    constructor ; [| solve_proper ].
    iIntros (φ1 φ2 Hφ1 Hφ2) "H %x HF1 HΦ". 
    by iApply "H"; iApply "HF1".
  Qed.

  Theorem fixpoint_existence : ∃ φ : A -d> siProp, φ ≡ F φ φ.
  Proof.
    exists (least_banach_fixpoint F).
    apply least_banach_fixpoint_unfold.
  Qed.
End example1.

Module example2.
  Parameter A : ofe.
  Definition F (Φ φ : A -d> siProp) : A -d> siProp := λ a, ((▷ (Φ a) → φ a) ∨ φ a)%I.

  Instance F_contractive n : Proper (dist_later n ==> dist n ==> dist n) F.
  Proof.
    intros φ1 φ2 Hφ x y Hxy a. rewrite /F /=.
    apply or_ne ; [| apply Hxy ].
    apply impl_ne ; [| apply Hxy].
    apply later_contractive.
    rewrite dist_later_fin_iff.
    destruct n ; [done| apply Hφ ; lia ].
  Qed.

  Instance F_proper : Proper ((≡) ==> (≡) ==> (≡)) F.
  Proof. solve_proper. Qed.

  Instance F_mono : ∀ Φ : A -n> siProp, BiMonoPred (F Φ).
  Proof.
    constructor ; [| solve_proper ].
    iIntros (φ1 φ2 Hφ1 Hφ2) "H %x HF1". 
    iDestruct "HF1" as "[HF1|HF1]".
    - iLeft. iIntros "HΦ". by iApply "H"; iApply "HF1".
    - iRight. by iApply "H".
  Qed.

  Theorem fixpoint_existence : ∃ φ : A -d> siProp, φ ≡ F φ φ.
  Proof.
    exists (least_banach_fixpoint F).
    apply least_banach_fixpoint_unfold.
  Qed.
End example2.
