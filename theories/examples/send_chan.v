From dlfactris.base_logic Require Import proofmode.
From dlfactris.lang Require Import notation.

Definition send_chan : val := λ: <>,
  let: "c" := ForkChan (λ: "ch",
              let: "d" := ForkChan (λ: "dh", Send "dh" #0 ) in
              Send "ch" "d" ) in
  let: "d" := Recv "c" in
  Recv "d".

Definition send_chan_prot1 : aMiniProt :=
  {| prot_action := ARecv;
     prot_pred := λ v, ⌜⌜v = #0⌝⌝%I |}.

Definition send_chan_prot2 : aMiniProt :=
  {| prot_action := ARecv;
     prot_pred := λ v, (∃ l : loc, ⌜⌜ v = #l ⌝⌝ ∗ own_chan l send_chan_prot1)%I |}.

Lemma send_chan_wp :
  ⊢ WP send_chan #() {{ v, ⌜⌜v = #0⌝⌝ }}.
Proof.
  wp_rec. iApply (wp_fork _ send_chan_prot2).
  - iIntros "!> %c Hc". wp_pures. 
    iApply (wp_fork _ send_chan_prot1).
    { iIntros "!> %d Hd". wp_pures.
      rewrite /send_chan_prot1 /dual /=.
      iApply (wp_send with "Hd") ; eauto. }
    iIntros "!> %d Hd". wp_pures.
    (* rewrite /send_chan_prot2 /dual /=. *)
    iApply (wp_send with "[Hc] [Hd]"); eauto.
    iNext. rewrite /send_chan_prot2 /=. 
    iExists d. by iFrame.
  - iIntros "!> %d Hd". wp_pures.
    iApply (wp_recv with "Hd").
    iIntros "!>" (l) "Hd". wp_pures.
    by iApply (wp_recv with "Hd").
Qed.

Lemma send_chan_spec :
  {{{ emp }}} send_chan #() {{{ RET #0; emp }}}.
Proof.
  iIntros (Φ) "_ HΦ". 
  iApply send_chan_wp. 
  by iApply "HΦ". 
Qed.

              
  
