From dlfactris.base_logic Require Import proofmode.
From dlfactris.lang Require Import notation.

Definition swap : val :=
  λ: "x" "y",
    let: "tmp" := !"x" in
    "x" <- !"y";;
    "y" <- "tmp".

Lemma wp_swap  (l1 l2 : loc) v1 v2 :
l1 ↦ v1 ∗ l2 ↦ v2 ⊢ WP (swap #l1 #l2) {{ v, ⌜⌜ v = #() ⌝⌝ ∗ l1 ↦ v2 ∗ l2 ↦ v1 }}.
Proof.
  iIntros "[H1 H2]".
  wp_rec!. wp_load!. 
  wp_load!. wp_store!. wp_store.
  by iFrame.
Qed.

Lemma swap_spec (l1 l2 : loc) v1 v2 :
  {{{ l1 ↦ v1 ∗ l2 ↦ v2 }}}
    swap #l1 #l2
  {{{ RET #(); l1 ↦ v2 ∗ l2 ↦ v1 }}}.
Proof.
  iIntros (Φ) "[H1 H2] HΦ".
  iApply (wp_wand with "[H1 H2]").
  - iApply wp_swap; iFrame.
  - iIntros (v) "(-> & H1 & H2)". iApply "HΦ".
    iFrame.
Qed.
