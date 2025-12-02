From dlfactris.base_logic Require Import proofmode.
From dlfactris.lang Require Import notation.

Definition send_recv : val := λ: <>,
  let: "c" := ForkChan (λ: "ch",
              let: "l" := Alloc #10 in
              Send "ch" "l" ) in
  let: "l" := Recv "c" in
  let: "v" := ! "l" in
  Free "l" ;; "v" + #1.

Definition send_recv_prot : aMiniProt :=
  {| prot_action := ARecv;
     prot_pred := λ v, (∃ l : loc, ⌜⌜ v = #l ⌝⌝ ∗ l ↦ #10)%I |}.


Lemma send_recv_wp :
  ⊢ WP send_recv #() {{ v, ⌜⌜v = #11⌝⌝ }}.
Proof.
  wp_rec. iApply (wp_fork _ send_recv_prot).
  - iIntros "!> %c Hc". wp_pures. 
    wp_alloc l as "Hl".
    wp_pures. iApply (wp_send with "[Hc] [Hl]") ; eauto.
    iNext. iExists l. by iFrame.
  - iIntros "!> %d Hd". wp_pures.
    iApply (wp_recv with "Hd").
    iIntros "!>" (l) "Hd". wp_pures.
    wp_load. wp_pures. wp_free.
    by wp_pures.
Qed.

Lemma send_recv_spec :
  {{{ emp }}} send_recv #() {{{ RET #11; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". 
  iApply send_recv_wp.
  by iApply "HΦ". 
Qed.

              
  
