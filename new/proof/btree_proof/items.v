From New.generatedproof Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.btree_proof Require Import btree_init rep.
From New.proof.sort_proof Require Import search.

(** * Specs for [items] slice helper methods. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx: GoContext}.

(** Pure predicate for [sort.Search]: [f(i) = true] iff [R key items[i]]. *)
Definition find_f (R : interface.t → interface.t → Prop) `{!RelDecision R}
    (key : interface.t) (items : list interface.t) : Z → bool :=
  λ i, match items !! (Z.to_nat i) with
       | Some x => bool_decide (R key x)
       | None => true
       end.

Lemma find_f_true R `{!RelDecision R} key items_list i x :
  items_list !! (Z.to_nat i) = Some x →
  find_f R key items_list i = true ↔ R key x.
Proof.
  rewrite /find_f. intros ->. rewrite bool_decide_eq_true //.
Qed.

Lemma find_f_false R `{!RelDecision R} key items_list i x :
  items_list !! (Z.to_nat i) = Some x →
  find_f R key items_list i = false ↔ ¬R key x.
Proof.
  rewrite /find_f. intros ->. rewrite bool_decide_eq_false //.
Qed.

Local Transparent btree.items btree.Item.
Local Typeclasses Transparent btree.items btree.Item.

Lemma wp_items__find (sl : slice.t) (items_list : list interface.t)
    (key : interface.t) (R : interface.t → interface.t → Prop)
    `{!RelDecision R, !Transitive R} :
  {{{ is_pkg_init btree ∗
      sl ↦* items_list ∗
      is_less_order R ∗
      ⌜items_sorted R items_list⌝ ∗
      ⌜key ≠ interface.nil⌝ ∗
      ⌜Forall (λ x, x ≠ interface.nil) items_list⌝ }}}
    sl @ btree.items.id @ "find"%go #key
  {{{ (idx : w64) (found : bool), RET (#idx, #found);
      sl ↦* items_list ∗
      ⌜if found then
         ∃ e, items_list !! uint.nat idx = Some e ∧ ¬R e key ∧ ¬R key e
       else
         (∀ j e, items_list !! j = Some e → (j < uint.nat idx)%nat → R e key) ∧
         (∀ j e, items_list !! j = Some e → (uint.nat idx ≤ j)%nat → R key e)⌝ }}}.
Proof.
  wp_start as "(Hsl & #Hless & %Hsorted & %Hkey_nn & %Hnn)".
  iDestruct (own_slice_len with "Hsl") as %Hlen.
  wp_auto.

  (* Apply sort.Search *)
  set (f := find_f R key items_list).
  set (I := (s_ptr ↦ sl ∗ item_ptr ↦ key ∗ sl ↦* items_list)%I).
  wp_apply (wp_Search _ _ f I with "[Hsl s item]").
  {
    iFrame.
    iSplit.
    { iPureIntro. word. }
    iSplit.
    - (* pred_implements *)
      iIntros (idx_w). wp_start as "((Hs & Hitem & Hsl) & %Hbound)".
      wp_auto.
      wp_alloc i as "Hi".
      wp_auto.
      list_elem items_list (sint.Z idx_w) as xi.
      wp_apply (wp_load_slice_elem with "[$Hsl]") as "Hsl".
      { word. } { iPureIntro. exact Hxi_lookup. }
      assert (xi ≠ interface.nil) as Hxi_nn by (eapply (Forall_lookup_1 _ _ _ _ Hnn Hxi_lookup)).
      wp_apply ("Hless" $! key xi with "[//] [//]").
      iIntros (b) "%Hb".
      wp_auto.
      iApply "HΦ". iFrame. iPureIntro.
      rewrite /f /find_f.
      replace (Z.to_nat (sint.Z idx_w)) with (sint.nat idx_w) by word.
      rewrite Hxi_lookup.
      destruct b; symmetry.
      + apply bool_decide_eq_true. apply Hb. done.
      + apply bool_decide_eq_false. intro. apply Hb. done.
    - iPureIntro.
      (* is_mono_pred *)
      rewrite /is_mono_pred /f /find_f.
      intros i j (Hi & Hij & Hj) Hfi.
      list_elem items_list (Z.to_nat i) as xi.
      list_elem items_list (Z.to_nat j) as xj.
      rewrite Hxi_lookup in Hfi.
      rewrite Hxj_lookup.
      apply bool_decide_eq_true in Hfi.
      apply bool_decide_eq_true.
      eapply transitivity; eauto.
      apply Hsorted with (i:=Z.to_nat i) (j:=Z.to_nat j); try lia; eauto.
  }

  (* Post-Search *)
  iIntros (i) "(HI & %Hi_nn & %Hfound & %Hoob & %Hbelow)".
  iDestruct "HI" as "(Hs & Hitem & Hsl)".
  wp_auto.

  assert (sint.Z i ≤ sint.Z sl.(slice.len_f)) as Hi_le.
  { destruct (decide (sint.Z i < sint.Z sl.(slice.len_f))); [lia|].
    assert (sint.Z i = sint.Z sl.(slice.len_f)); [|lia].
    apply Hoob. intros k Hk. apply Hbelow. lia. }

  wp_if_destruct.
  - (* i > 0 — check !items[i-1].Less(key) *)
    list_elem items_list (sint.nat (word.sub i (W64 1))) as xi_prev.
    wp_pure.
    { word. }
    wp_apply (wp_load_slice_elem with "[$Hsl //]") as "Hsl".
    { word. }
    assert (xi_prev ≠ interface.nil) as Hxi_prev_nn
      by (eapply (Forall_lookup_1 _ _ _ _ Hnn Hxi_prev_lookup)).
    wp_apply ("Hless" $! xi_prev key with "[//] [//]").
    iIntros (b) "%Hb".
    wp_auto.
    wp_if_destruct.
    + (* b=true, R xi_prev key → ~b=false → else branch → not found, return (i, false) *)
      iApply "HΦ". iFrame. iPureIntro.
      assert (R xi_prev key) as Hprev_lt by naive_solver.
      split.
      * intros j e Hj_lookup Hj_lt.
        destruct (decide (j = sint.nat (word.sub i (W64 1)))).
        { subst. replace e with xi_prev by
            (rewrite Hxi_prev_lookup in Hj_lookup; congruence). done. }
        { eapply transitivity; eauto.
          apply Hsorted with (i:=j) (j:=sint.nat (word.sub i (W64 1)));
            try word; eauto. }
      * intros j e Hj_lookup Hj_ge.
        destruct (decide (sint.Z i < sint.Z sl.(slice.len_f))).
        { assert (find_f R key items_list (sint.Z i) = true) as Hfi
            by (apply Hfound; word).
          destruct (decide (j = uint.nat i)).
          { subst. rewrite /f /find_f in Hfi.
            replace (Z.to_nat (sint.Z i)) with (uint.nat i) in Hfi by word.
            rewrite Hj_lookup in Hfi.
            apply bool_decide_eq_true in Hfi. done. }
          { list_elem items_list (uint.nat i) as x_i.
            assert (R key x_i).
            { apply (find_f_true R key items_list (sint.Z i) x_i).
              { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. eauto. }
              apply Hfound. word. }
            eapply transitivity; eauto.
            apply Hsorted with (i:=uint.nat i) (j:=j); try lia; eauto. } }
        { exfalso. apply lookup_lt_Some in Hj_lookup. word. }
    + (* b=false, ¬R xi_prev key → ~b=true → then branch → found, return (i-1, true) *)
      iApply "HΦ". iFrame. iPureIntro.
      assert (¬R xi_prev key) as Hnot_less by naive_solver.
      assert (¬R key xi_prev) as Hnot_less2.
      { apply (find_f_false R key items_list (sint.Z (word.sub i (W64 1))) xi_prev).
        { replace (Z.to_nat (sint.Z (word.sub i (W64 1)))) with
            (sint.nat (word.sub i (W64 1))) by word. eauto. }
        apply Hbelow. word. }
      exists xi_prev. split; [|split]; eauto.
      replace (uint.nat (word.sub i (W64 1))) with
        (sint.nat (word.sub i (W64 1))) by word. eauto.
  - (* i = 0 — not found, return (i, false) *)
    iApply "HΦ". iFrame. iPureIntro.
    split.
    + intros j e Hj_lookup Hj_lt. exfalso. word.
    + intros j e Hj_lookup Hj_ge.
      assert (uint.nat i = 0%nat) as Hi0 by word.
      destruct (decide (sint.Z i < sint.Z sl.(slice.len_f))).
      { assert (find_f R key items_list (sint.Z i) = true) as Hfi
          by (apply Hfound; word).
        destruct (decide (j = 0%nat)).
        { subst. rewrite /f /find_f in Hfi.
          replace (Z.to_nat (sint.Z i)) with 0%nat in Hfi by word.
          rewrite Hj_lookup in Hfi.
          apply bool_decide_eq_true in Hfi. done. }
        { list_elem items_list (0%nat) as x0.
          assert (R key x0).
          { apply (find_f_true R key items_list (sint.Z i) x0).
            { replace (Z.to_nat (sint.Z i)) with 0%nat by word. eauto. }
            apply Hfound. word. }
          eapply transitivity; eauto.
          apply Hsorted with (i:=0%nat) (j:=j); try word; eauto. } }
      { exfalso. apply lookup_lt_Some in Hj_lookup. word. }
Qed.

End proof.
