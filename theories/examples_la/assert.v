From dlfactris.base_logic Require Import proofmode.
From dlfactris.lang Require Import notation.

(* This file is taken integrally from the LinearActris framework (Linear Actris
   Artifact. Zenodo. https://doi.org/10.5281/zenodo.8422755) and works verbatim
   in LiveActris.
*)

Definition assert : val :=
  λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)
(* just below ;; *)
Notation "'assert:' e" := (assert (λ: <>, e)%E) (at level 99) : expr_scope.
Notation "'assert:' e" := (assert (λ: <>, e)%V) (at level 99) : val_scope.

Lemma wp_assert (Φ : val → aProp) e :
  WP e {{ v, ⌜v = #true⌝ ∧ Φ #() }} -∗
  WP (assert: e)%V {{ Φ }}.
Proof.
  iIntros "HΦ". wp_rec. iApply (wp_wand with "HΦ"). iIntros (v) "[% ?]"; subst.
  by wp_pures.
Qed.
