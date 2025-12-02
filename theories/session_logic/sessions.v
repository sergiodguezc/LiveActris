From dlfactris.session_logic Require Export sub.

Module Ses.
  Definition fork_chan : val := Sub.fork_chan.
  Definition recv : val := Sub.recv.
  Definition send : val := λ: "c" "v",
    Sub.fork_chan (λ: "c'", Sub.send "c" ("v", "c'")).
  Definition close : val := λ: "c", Sub.send "c" #().
  Definition wait := Sub.recv.

  Notation prot := Sub.prot.
  Notation dual := Sub.dual.
  Notation subprot := Sub.subprot.
  Notation own_chan := Sub.own_chan.

  Module Import notations := Sub.notations.

  Notation subprot_refl := Sub.subprot_refl.
  Notation subprot_trans := Sub.subprot_trans.
  Notation subprot_dual := Sub.subprot_dual.
  Notation own_chan_subprot := Sub.own_chan_subprot.

  Definition end_prot (a : action) (P : aProp) : prot :=                         (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=5973985d *)
    MiniProt a (λ r, ⌜⌜ r = #() ⌝⌝ ∗ P)%I.
  Global Instance: Params (@end_prot) 1 := {}.

  Definition msg_prot (a : action) {A}                                           (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=423aeac8 *)
      (v : A → val) (P : A → aProp) (p : A → prot) : prot :=
    MiniProt a (λ r, ∃ x c,
      ⌜⌜ r = (v x, c)%V ⌝⌝ ∗ P x ∗
      Sub.own_chan c (if a is ARecv then p x else dual (p x)))%I.
  Global Instance: Params (@msg_prot) 2 := {}.

  Global Instance msg_end_ne a : NonExpansive (end_prot a).
  Proof. solve_proper. Qed.
  Global Instance msg_end_proper a : Proper ((≡) ==> (≡)) (end_prot a).
  Proof. apply: ne_proper. Qed.

  Global Instance msg_prot_contractive {A} a n :
    Proper (pointwise_relation A (=) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) (msg_prot a).
  Proof. solve_contractive. Qed.
  Global Instance msg_prot_ne {A} a n :
    Proper (pointwise_relation A (=) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) (msg_prot a).
  Proof. solve_proper. Qed.
  Global Instance msg_prot_proper {A} a :
    Proper (pointwise_relation A (=) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) (msg_prot a).
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq; apply equiv_dist=> n.
    f_equiv; [done|..]=> x; apply equiv_dist; auto.
  Qed.

  (** WPs for session channels *)
  Lemma wp_fork_chan p (f : val) Ψ :
    ▷ (∀ c, c ↣ dual p -∗ WP f c {{ _, emp }}) -∗
    ▷ (∀ c, c ↣ p -∗ Ψ c) -∗
    WP fork_chan f {{ Ψ }}.
  Proof. apply Sub.wp_fork_chan. Qed.

  Lemma wp_recv {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) Ψ :
    c ↣ msg_prot ARecv v P p -∗ ▷ (∀ w, (∃ c', ∃ x, ⌜⌜ w = (v x, c')%V ⌝⌝ ∗ c' ↣ p x ∗ P x) -∗ Ψ w) -∗
    WP recv c {{ Ψ }}.
  Proof.
    iIntros "Hc Hwand". iApply (Sub.wp_recv with "Hc"). 
    iIntros "!>" (v') "(%x & %c' & -> & HP & Hc')".
    iApply "Hwand". 
    eauto with iFrame.
  Qed.

  Lemma wp_send {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) x Ψ :
    c ↣ msg_prot ASend v P p -∗ P x -∗ ▷ (∀ c', c' ↣ p x -∗ Ψ c') -∗
    WP send c (v x) {{ Ψ }}.
  Proof.
    iIntros "Hc HP HΨ". wp_rec. iApply (Sub.wp_fork_chan with "[Hc HP]"); iIntros "!>" (c') "Hc'".
    - wp_pures. iApply (Sub.wp_send with "Hc [-]"); last done.
      iExists x, c'. by iFrame.
    - iApply "HΨ"; iFrame.
  Qed.

  Lemma wp_wait c P Ψ :
    c ↣ end_prot ARecv P -∗ ▷ (P -∗ Ψ #()) -∗
      WP wait c {{ Ψ }}.
  Proof.
    iIntros "Hc Hwand". iApply (Sub.wp_recv with "Hc").
    iIntros "!>" (v) "(-> & HP)". by iApply "Hwand". 
  Qed.

  Lemma wp_close c P Ψ :
    c ↣ end_prot ASend P -∗ P -∗ ▷ Ψ #() -∗
    WP close c {{ Ψ }}.
  Proof.
    iIntros "Hc HP HΨ".
    wp_rec. iApply (Sub.wp_send with "Hc [HP]"); by iFrame.
  Qed.

  Global Opaque fork_chan recv send close wait.
  Global Typeclasses Opaque end_prot msg_prot.
End Ses.
