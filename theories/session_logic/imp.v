From dlfactris.session_logic Require Export sessions.

Module Imp.
  Definition fork_chan : val := λ: "f",                                          (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=f0b10cb3 *)
    Alloc $ Ses.fork_chan (λ: "c2", "f" (Alloc "c2")).

  Definition recv : val := λ: "c",
    let: '("v","r") := Ses.recv !"c" in
    "c" <- "r";; "v".

  Definition send : val := λ: "c" "v",
    "c" <- Ses.send (!"c") "v".

  Definition close : val := λ: "c",
    Ses.close !"c";; Free "c".

  Definition wait : val := λ: "c",
    Ses.wait !"c";; Free  "c".

  Notation prot := Ses.prot.
  Notation dual := Ses.dual.
  Notation end_prot := Ses.end_prot.
  Notation msg_prot := Ses.msg_prot.
  Notation subprot := Ses.subprot.

  Definition own_chan (c : val) (p : aMiniProt) : aProp :=
    ∃ (l : loc) ch, ⌜⌜ c = #l ⌝⌝ ∗ l ↦ ch ∗ Ses.own_chan ch p.

  Module Import notations.
    Notation "p ⊑ q" := (subprot p q) : bi_scope.
    Notation "c ↣ p" := (own_chan c p) : bi_scope.
  End notations.

  Notation subprot_refl := Ses.subprot_refl.
  Notation subprot_trans := Ses.subprot_trans.
  Notation subprot_dual := Ses.subprot_dual.

  Global Instance own_chan_contractive ch : Contractive (own_chan ch).
  Proof. solve_contractive. Qed.
  Global Instance own_chan_ne ch : NonExpansive (own_chan ch).
  Proof. solve_proper. Qed.
  Global Instance own_chan_proper ch : Proper ((≡) ==> (≡)) (own_chan ch).
  Proof. solve_proper. Qed.

  Lemma own_chan_subprot c p1 p2 : c ↣ p1 -∗ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) Hsp". iExists l, ch.
    iSplit; [done|]. iFrame. by iApply (Ses.own_chan_subprot with "Hch").
  Qed.

  Lemma wp_fork_chan p (f : val) Ψ :                                               (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=a3e914ff *)
    ▷ (∀ c, c ↣ dual p -∗ WP f c {{ _, emp }}) -∗
    ▷ (∀ c, c ↣ p -∗ Ψ c) -∗
    WP fork_chan f {{ Ψ }}.
  Proof.
    iIntros "Hf Hwand". wp_rec!.
    iApply wp_bind.
    { apply Ctx_compose ; [constructor | by apply Ctx_id]. }

    iApply (Ses.wp_fork_chan with "[Hf]") ; iIntros "!>" (c) "Hc".
    {  wp_alloc l as "Hl". iApply "Hf".
      iExists l, c. by iFrame. }
    wp_alloc l as "Hl". iApply "Hwand". by iFrame.
  Qed.

  Lemma wp_recv {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) Ψ :
    c ↣ msg_prot ARecv v P p -∗
    ▷ (∀ w, (∃ x, ⌜⌜ w = v x ⌝⌝ ∗ c ↣ p x ∗ P x ) -∗ Ψ w) -∗
    WP recv c {{ Ψ }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) Hwand". wp_rec!. wp_load.
    iApply (Ses.wp_recv with "Hch"). iIntros "!>" (w) "H".
    iDestruct "H" as (ch' x) "[-> [Hch' HP]]".
    wp_store!. iApply "Hwand".
    by iFrame.
  Qed.

  Lemma wp_send {A} c (v : A → val) (P : A → aProp) (p : A → aMiniProt) x Ψ :
    c ↣ msg_prot ASend v P p -∗ P x -∗ ▷ (c ↣ p x -∗ Ψ #()) -∗
    WP send c (v x) {{ Ψ }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) HP Hwand". wp_rec!. wp_load.
    iApply (Ses.wp_send with "Hch HP"). iIntros "!>" (ch') "Hch'".
    wp_store. iApply "Hwand".
    by iFrame.
  Qed.

  Lemma wp_wait c P Ψ :
    c ↣ end_prot ARecv P -∗ ▷ (P -∗ Ψ #()) -∗
    WP wait c {{ Ψ }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) Hwand". wp_rec!. wp_load.
    iApply (Ses.wp_wait with "Hch"); iIntros "!> HP". wp_free.
    iApply "Hwand". by iFrame.
  Qed.

  Lemma wp_close c P Ψ :
    c ↣ end_prot ASend P -∗ P -∗ ▷ Ψ #() -∗
    WP close c {{ Ψ }}.
  Proof.
    iIntros "(%l & %ch & -> & Hl & Hch) HP HΨ". wp_rec!. wp_load.
    iApply (Ses.wp_close with "Hch HP"). iNext. by wp_free.
  Qed.

  Global Opaque fork_chan recv send close wait.
  Global Opaque own_chan.
End Imp.
