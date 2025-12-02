From Coq Require Import List.
From dlfactris.base_logic Require Import proofmode.
From dlfactris.lang Require Import lang notation.

From dlfactris.examples_la Require Import llist.

Definition find : val :=
  rec: "go" "l" "x" := 
    match: !"l" with
    | "nil" <> => #false
    | "cons" "t" =>
        let: '("hd", "tl") := "t" in
        if: "hd" = "x" then #true else "go" "tl" "x"
    end.

Section find.
  Implicit Types xs : list val.
  Implicit Types l : loc.
  Implicit Types x : val.
  Local Arguments llist {_} _ _ !_ /.

  Local Instance Val_In_dec (a : val) (xs : list val) :
    Decision (In a xs).
  Proof. apply In_dec. solve_decision. Qed.

  Definition eqI (x y : val) : aProp := ⌜⌜ x = y ⌝⌝%I.
  
  Lemma wp_find xs l x :
    llist eqI l xs -∗ WP (find #l x) {{ w, ⌜⌜ w = #(bool_decide (In x xs)) ⌝⌝ ∗ llist eqI l xs }}.
  Proof.
    iRevert (l x).
    iInduction xs as [|hd tl] "IH" ; iIntros (l x) "Hlist".
    - wp_rec!. wp_load! . iFrame. simpl. rewrite bool_decide_false //. eauto.
    - wp_rec!. iDestruct "Hlist" as (t l') "[%Hl' [Hcons Htl]]".
      wp_load!.
      destruct (decide (t = x)) as [->|Hneq].
      + rewrite bool_decide_true //.
        wp_pure. 
        iFrame. rewrite Hl'. iSplitR ; last by eauto.
        rewrite bool_decide_true /= //; eauto.
      + rewrite bool_decide_false //.
        wp_pure.
        iApply ("IH" with "[Htl]") ; eauto.
        iIntros "H". iFrame. iSplitR ; last auto.
        subst.
        destruct (decide (In x tl)). 
        * rewrite !bool_decide_true //=. eauto.
        * rewrite !bool_decide_false //=. intros [Hc|Hc]; eauto.
  Qed.
      
Lemma find_spec xs l x :
  {{{ llist eqI l xs }}}
    find #l x
  {{{ w, RET w; ⌜⌜ w = #(bool_decide (In x xs)) ⌝⌝ ∗ llist eqI l xs }}}.
Proof.
  iIntros (Φ) "Hlist HΦ".
  iApply (wp_find with "Hlist").
  iIntros "Hlist".
  iApply "HΦ". iFrame. eauto.
Qed.

End find.
