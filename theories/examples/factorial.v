From dlfactris.base_logic Require Import proofmode.
From dlfactris.lang Require Import notation.

Definition factorial : val :=
  rec: "go" "v" := if: "v" = #0 then #1 else "v" * "go" ("v" - #1).

Lemma wp_factorial  (n : nat) :
⊢ WP (factorial #n) {{ v, ⌜⌜v = # (Z.of_nat (fact n))⌝⌝ }}.
Proof.
  iInduction n as [|n IH] "IH".
  - by wp_rec; wp_pures. 
  - wp_rec. wp_pures.
   replace (Z.sub (Z.of_nat (S n)) (Zpos xH)) with (Z.of_nat n) by lia.
   iApply "IH". wp_pures.
   replace (Z.mul (Z.of_nat (S n)) (Z.of_nat (fact n))) with (Z.of_nat (S n * fact n)) by lia.
   by replace (S n * fact n) with (fact (S n)) by done.
Qed.

Lemma factorial_spec (n : nat) :
{{{ emp }}} factorial #n {{{ RET #(Z.of_nat (fact n)); emp }}}.
Proof.
  iPoseProof (wp_factorial n) as "Hfact".
  iIntros (Φ) "Hemp HΦ".
  iApply (wp_wand with "Hfact").
  iIntros (v ->). by iApply "HΦ".
Qed.
