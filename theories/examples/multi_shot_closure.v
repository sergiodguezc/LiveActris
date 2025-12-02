From dlfactris.lang Require Import notation.
From dlfactris.session_logic Require Export proofmode.
Import TImp TImp.notations.

Definition multi_shot_closure : val := λ: <>,
  let: "c" := fork_chan (λ: "ch",
              let: "f" := recv "ch" in
              let: "w" := "f" #0 in
              send "ch" "w" ;;
              wait "ch") in
      send "c" (λ: "x", "x" + #1) ;;
      let: "result" := recv "c" in
      close "c" ;; "result".

Definition multi_shot_closure_prot : prot :=
  <! (f : val) (Φ : val → aProp)> MSG f {{ WP f #0 {{ v, Φ v }} }} ;
  <? (v : val)> MSG v {{ Φ v }} ; END!.

Lemma multi_shot_closure_wp :
  ⊢ WP multi_shot_closure #() {{ v, ⌜⌜ v = #1 ⌝⌝ }}.
Proof.
  wp_rec!.
  iApply (wp_fork_chan multi_shot_closure_prot).
  - iIntros "!>" (c) "Hc"; wp_pures.
    wp_recv (f Φ) as "Hwp" ; wp_pures.
    iApply "Hwp".
    iIntros (v) "HΦ" ; wp_pures.
    wp_send with "[$HΦ]".
    by wp_wait.
  - iIntros "!>" (c) "Hc"; wp_pures.
    iAssert (WP (λ: "x", "x" + #1)%V #0 {{ v, ⌜⌜ v = #1 ⌝⌝ }})%I as "Hwp".
    { by wp_pures. }
    wp_send with "[$Hwp]".
    wp_recv (v) as "HΦ" ; wp_pures.
    by wp_close!.
Qed.

Lemma multi_shot_closure_spec :
  {{{ emp }}}
    multi_shot_closure #()
  {{{ v, RET v; ⌜⌜ v = #1 ⌝⌝ }}}.
Proof.
  iIntros (Φ) "_ Hwp".
  iApply multi_shot_closure_wp.
  by iApply "Hwp".
Qed.
