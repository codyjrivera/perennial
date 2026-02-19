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
  (* BLOCKED: wp_auto cannot step through exception_do in closures/the
     outer function body. The proof sketch below is preserved as a comment.
     See hypotheses at the pred_implements admit for debugging leads.

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
      change btree.Item with interfaceT.
      change btree.items with sliceT.
      (* STUCK: wp_auto fails with "Failed to progress" on the goal:
         WP exception_do (let: "i" := alloc (# idx_w) in
           return: (let: "$a0" := ![#interfaceT] (slice.elem_ref ...) in
             interface.get #"Less" ![#interfaceT] (# item_ptr) "$a0"))
         {{ v, Φ v }}

         Hypothesis 1: wp_pure fails to beta-reduce #f_code #idx_w.
         Hypothesis 2: wp_alloc_auto can't find alloc inside exception_do's
           AppRCtx (sealed val issue?).
         Hypothesis 3: change doesn't fully rewrite all type occurrences,
           blocking typeclass resolution in tac_wp_alloc or IntoVal.

         Next steps to try:
         1. Manual tactics: wp_call_lc "?". wp_alloc i_ptr as "Hi". ...
         2. rewrite exception_do_unseal. wp_auto.
         3. wp_bind (exception_do). ...
         4. Compare with sort_proof/search.v:281 interactively.
      *)
      admit.
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

  iIntros (i) "(HI & %Hi_nn & %Hfound & %Hoob & %Hbelow)".
  iDestruct "HI" as "(Hs & Hitem & Hsl)".
  wp_auto.

  (* Now handle the if: i > 0 && !items[i-1].Less(key) *)
  (* First: i > 0? *)
  wp_if_destruct.
  - (* i > 0 — need to check !items[i-1].Less(key) *)
    wp_auto.
    list_elem items_list (sint.nat (word.sub i (W64 1))) as xi_prev.
    wp_apply (wp_load_slice_elem with "[$Hsl]") as "Hsl".
    { word. }
    { eauto. }
    wp_apply ("Hless" with "[//] [//]").
    iIntros (b) "%Hb".
    wp_auto.
    wp_if_destruct.
    + (* !items[i-1].Less(key) = true, so ¬R items[i-1] key — found *)
      wp_auto.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      assert (¬R xi_prev key) as Hnot_less by naive_solver.
      assert (¬R key xi_prev) as Hnot_less2.
      { apply (find_f_false R key items_list (sint.Z (word.sub i (W64 1))) xi_prev); eauto.
        { replace (Z.to_nat (sint.Z (word.sub i (W64 1)))) with
            (sint.nat (word.sub i (W64 1))) by word.
          eauto. }
        apply Hbelow. word. }
      exists xi_prev. split; [|split]; eauto.
      replace (uint.nat (word.sub i (W64 1))) with
        (sint.nat (word.sub i (W64 1))) by word.
      eauto.
    + (* items[i-1].Less(key) = true, so R items[i-1] key — not found *)
      wp_auto.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      assert (R xi_prev key) as Hprev_lt by naive_solver.
      split.
      * intros j e Hj_lookup Hj_lt.
        destruct (decide (j = sint.nat (word.sub i (W64 1)))).
        { subst. replace e with xi_prev by (rewrite Hxi_prev_lookup in Hj_lookup; congruence). done. }
        { eapply transitivity; eauto.
          apply Hsorted with (i:=j) (j:=sint.nat (word.sub i (W64 1))); try lia; eauto. }
      * intros j e Hj_lookup Hj_ge.
        destruct (decide (sint.Z i < sint.Z sl.(slice.len_f))).
        { assert (find_f R key items_list (sint.Z i) = true) as Hfi.
          { apply Hfound. word. }
          destruct (decide (j = uint.nat i)).
          { subst. rewrite /f /find_f in Hfi.
            replace (Z.to_nat (sint.Z i)) with (uint.nat i) in Hfi by word.
            rewrite Hj_lookup in Hfi.
            apply bool_decide_eq_true in Hfi. done. }
          { list_elem items_list (uint.nat i) as x_i.
            assert (R key x_i).
            { rewrite find_f_true; [|replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word; eauto].
              apply Hfound. word. }
            eapply transitivity; eauto.
            apply Hsorted with (i:=uint.nat i) (j:=j); try lia; eauto. } }
        { exfalso. apply lookup_lt_Some in Hj_lookup. word. }
  - (* i = 0 — not found *)
    wp_auto.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split.
    + intros j e Hj_lookup Hj_lt. lia.
    + intros j e Hj_lookup Hj_ge.
      assert (uint.nat i = 0) as Hi0 by word.
      destruct (decide (sint.Z i < sint.Z sl.(slice.len_f))).
      { assert (find_f R key items_list (sint.Z i) = true) as Hfi.
        { apply Hfound. word. }
        destruct (decide (j = 0)).
        { subst. rewrite /f /find_f in Hfi.
          replace (Z.to_nat (sint.Z i)) with 0%nat in Hfi by word.
          rewrite Hj_lookup in Hfi.
          apply bool_decide_eq_true in Hfi. done. }
        { list_elem items_list 0 as x0.
          assert (R key x0).
          { rewrite find_f_true; [|replace (Z.to_nat (sint.Z i)) with 0%nat by word; eauto].
            apply Hfound. word. }
          eapply transitivity; eauto.
          apply Hsorted with (i:=0%nat) (j:=j); try lia; eauto. } }
      { exfalso. apply lookup_lt_Some in Hj_lookup. word. }
  *)
Admitted.

End proof.
