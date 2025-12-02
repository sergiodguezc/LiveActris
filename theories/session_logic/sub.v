From dlfactris.lang Require Export notation.
From dlfactris.base_logic Require Export proofmode.

Module Sub.
  Notation prot := aMiniProt.
  Notation dual := dual.

  Definition fork_chan : val := λ: "f", ForkChan "f".
  Definition recv : val := λ: "c", Recv "c".
  Definition send : val := λ: "c" "x", Send "c" "x".

  Definition subprot (p1 p2 : aMiniProt) : aProp :=                              (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=923fd1fb *)
    match prot_action p1, prot_action p2 with
    | ASend, ASend => ∀ v, p2 v -∗ p1 v
    | ARecv, ARecv => ∀ v, p1 v -∗ p2 v
    | _, _ => False
    end.

  Definition own_chan (c : val) (p : prot) : aProp :=
    ∃ (l : loc) p', ⌜⌜ c = #l ⌝⌝ ∗ ▷ subprot p' p ∗ own_chan l p'.
  Global Instance: Params (@own_chan) 1 := {}.

  Global Instance subprot_ne : NonExpansive2 subprot.
  Proof.
    intros ? [??] [??] [??] [??] [??] [??]; simplify_eq/=.
    rewrite /subprot /=. by repeat f_equiv.
  Qed.
  Global Instance subprot_proper : Proper ((≡) ==> (≡) ==> (≡)) subprot.
  Proof. apply ne_proper_2, _. Qed.

  Global Instance own_chan_contractive c : Contractive (own_chan c).
  Proof. solve_contractive. Qed.
  Global Instance own_chan_ne c : NonExpansive (own_chan c).
  Proof. solve_proper. Qed.
  Global Instance own_chan_proper c : Proper ((≡) ==> (≡)) (own_chan c).
  Proof. solve_proper. Qed.

  Module Import notations.
    Notation "p ⊑ q" := (subprot p q) : bi_scope.
    Notation "c ↣ p" := (own_chan c p) : bi_scope.
  End notations.

  Lemma subprot_refl p : ⊢ p ⊑ p.
  Proof. destruct p as [[] Φ]; rewrite /subprot //=; auto. Qed.

  Lemma subprot_dual p1 p2 : dual p1 ⊑ dual p2 ⊣⊢ p2 ⊑ p1.
  Proof. destruct p1 as [[]], p2 as [[]]; auto. Qed.

  Lemma subprot_trans p1 p2 p3 : p1 ⊑ p2 -∗ p2 ⊑ p3 -∗ p1 ⊑ p3.
  Proof.
    iIntros "Hsp1 Hsp2".
    destruct p1 as [[] P1], p2 as [[] P2], p3 as [[] P3];
      rewrite /subprot //=; iIntros (v) "H //";
      by do 2 (iApply "Hsp1" || iApply "Hsp2").
  Qed.

  Lemma own_chan_subprot c p p' : c ↣ p -∗ ▷ (p ⊑ p') -∗ c ↣ p'.
  Proof.
    iIntros "(%l & %p'' & -> & Hsp' & Hc) Hsp".
    iExists l, p''. iSplit; [done|]. iFrame.
    by iApply (subprot_trans with "Hsp'").
  Qed.

  Local Lemma own_chan_from_base l p : aprop.own_chan l p ⊢ #l ↣ p.
  Proof.
    iIntros "Hown".
    iExists l, p. iSplit; [done|]. iFrame. iApply subprot_refl.
  Qed.

  (** WP's for own_chan_sub *)
  Lemma wp_fork_chan p (f : val) Ψ :
    ▷ (∀ c, c ↣ dual p -∗ WP f c {{ _, emp }}) -∗
    ▷ (∀ c, c ↣ p -∗ Ψ c) -∗
    WP fork_chan f {{ Ψ }}.
  Proof.
    iIntros "Hf Hwand". wp_rec.
    iApply (wp_fork with "[Hf]") ; iIntros "!>" (l) "Hown" . 
    - iApply "Hf" .
      by iApply own_chan_from_base.
    - iApply "Hwand".
      by iApply own_chan_from_base.
  Qed.

  Lemma wp_recv c Φ Ψ :
    c ↣ MiniProt ARecv Φ -∗ ▷ (∀ v, Φ v -∗ Ψ v) -∗
    WP recv c {{ Ψ }}.
  Proof.
    iIntros "(%l & %p' & -> & Hsp & Hc) Hwand". wp_rec.
    iApply is_except_0.
    destruct p' as [[] Ψ']; rewrite /subprot /=.
    - rewrite /bi_except_0; by iLeft.
    - iModIntro.
      iApply (wp_recv with "[$]").
      iIntros "!>" (v) "HΦ".
      iApply "Hwand". by iApply "Hsp".
  Qed.

  Lemma wp_send c v Φ Ψ :
    c ↣ MiniProt ASend Φ -∗ ▷ Φ v -∗ ▷ Ψ #() -∗
    WP send c v {{ Ψ }}.
  Proof.
    iIntros "(%l & %p' & -> & Hsp & Hc) HΦ HΨ".
    iApply is_except_0.
    destruct p' as [[] Ψ'] ; rewrite /subprot /=.
    - iModIntro.
      wp_rec. wp_pures.
      iApply (wp_send with "Hc [Hsp HΦ]") ; last done.
      iModIntro. by iApply "Hsp".
    - rewrite /bi_except_0; by iLeft.
  Qed.

  Global Opaque fork_chan send recv own_chan.
  Global Typeclasses Opaque subprot.
End Sub.
