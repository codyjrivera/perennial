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
  (* BLOCKED on pred_implements closure. Root cause analysis via rocq_step.py:
     -----------------------------------------------------------------
     The closure body contains an IMPURE operation (interface.get / method
     dispatch). In sort_proof/search.v:281 (SearchInts), the analogous
     closure body is pure (just an integer comparison), so wp_auto handles
     exception_do transparently via PureWp instances. Here, the Less method
     call breaks the PureWp chain.

     Diagnosis (confirmed with rocq_step.py intermediate states):
     1. wp_start succeeds — beta-reduces the closure application.
     2. wp_auto succeeds partially — allocates local vars, loads slice len,
        gets to: WP exception_do (let: "i" := alloc ... in return: (...)) {{ Φ }}
     3. wp_auto STOPS — can't step inside exception_do because:
        - exception_do is sealed (AppRCtx can't be decomposed)
        - The inner body has an impure step (interface.get), so the PureWp
          instance pure_exception_do_return_v doesn't fire (it needs the
          entire body to reduce to return_val v first)
     4. wp_bind can't help either — walk_expr in proofmode.v DOES traverse
        into AppRCtx, but wp_bind (alloc _)%E fails to match the pattern
        (possibly because alloc (# idx_w) is App (Val alloc) (Val idx_w)
        and walk_expr's App (Val _) (Val _) case goes left into Val, stopping).

     Attempted fixes:
     - rewrite exception_do_unseal: reveals (λ: "v", Snd "v") but wp_auto
       still can't step through (the lambda applied to non-value)
     - rewrite exception_do_unseal do_return_unseal: do_return is Local,
       can't unfold by name
     - wp_bind.: finds the closure call but not the inner expression
     - wp_bind (alloc _)%E: "could not find pattern"
     - iApply (wp_bind (fill [AppRCtx exception_do])): type mismatch
       between goose_ectxi_lang.expr and language.expr

     LIKELY FIX: Need a wp_exception_do_bind lemma or tactic that does
     iApply wp_bind with the right coercion for AppRCtx exception_do.
     This is a one-line lemma but requires getting the Iris type plumbing
     right. See items_test.v for the failed attempt. Alternatively, a
     framework-level fix in proofmode.v to make walk_expr / wp_auto aware
     of the exception_do evaluation context would fix all such closures.
     -----------------------------------------------------------------

     NOTE: The exception_do blocker affects the ENTIRE function body, not
     just the closure. After Search returns, the continuation is also inside
     exception_do, so wp_auto/wp_if_destruct fail there too.

     The proof sketch below is preserved as comments. The pre-Search setup
     (wp_start, wp_auto, set, wp_apply) and is_mono_pred all compile.
     The pred_implements closure and post-Search branches need the fix. *)

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
    - (* pred_implements — BLOCKED on exception_do, see note above.
         Once unblocked, the proof should be:
           wp_auto.  (* step through exception_do + alloc + loads *)
           list_elem items_list (sint.Z idx_w) as xi.
           wp_apply (wp_load_slice_elem with "[$Hsl]") as "Hsl".
           { word. } { rewrite Hxi_lookup. eauto. }
           wp_apply ("Hless" with "[//] [//]").
           iIntros (b) "%Hb".
           wp_auto.
           iApply "HΦ". iFrame. iPureIntro.
           rewrite /f /find_f Hxi_lookup.
           f_equal. apply bool_decide_ext. exact Hb. *)
      iIntros (idx_w). wp_start as "((Hs & Hitem & Hsl) & %Hbound)".
      admit.
    - iPureIntro.
      (* is_mono_pred — PROVED *)
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

  (* Post-Search — BLOCKED on exception_do (same issue, entire body is wrapped).
     Once the exception_do fix lands, the proof continues:

  iIntros (i) "(HI & %Hi_nn & %Hfound & %Hoob & %Hbelow)".
  iDestruct "HI" as "(Hs & Hitem & Hsl)".
  wp_auto.

  wp_if_destruct.
  - (* i > 0 — check !items[i-1].Less(key) *)
    wp_auto.
    list_elem items_list (sint.nat (word.sub i (W64 1))) as xi_prev.
    wp_apply (wp_load_slice_elem with "[$Hsl]") as "Hsl".
    { word. } { eauto. }
    wp_apply ("Hless" with "[//] [//]").
    iIntros (b) "%Hb".
    wp_auto.
    wp_if_destruct.
    + (* ¬Less → found *)
      wp_auto. iApply "HΦ". iFrame. iPureIntro.
      assert (¬R xi_prev key) as Hnot_less by naive_solver.
      assert (¬R key xi_prev) as Hnot_less2.
      { apply (find_f_false R key items_list (sint.Z (word.sub i (W64 1))) xi_prev); eauto.
        { replace (Z.to_nat (sint.Z (word.sub i (W64 1)))) with
            (sint.nat (word.sub i (W64 1))) by word. eauto. }
        apply Hbelow. word. }
      exists xi_prev. split; [|split]; eauto.
      replace (uint.nat (word.sub i (W64 1))) with
        (sint.nat (word.sub i (W64 1))) by word. eauto.
    + (* Less → not found *)
      wp_auto. iApply "HΦ". iFrame. iPureIntro.
      assert (R xi_prev key) as Hprev_lt by naive_solver.
      split.
      * intros j e Hj_lookup Hj_lt.
        destruct (decide (j = sint.nat (word.sub i (W64 1)))).
        { subst. replace e with xi_prev by
            (rewrite Hxi_prev_lookup in Hj_lookup; congruence). done. }
        { eapply transitivity; eauto.
          apply Hsorted with (i:=j) (j:=sint.nat (word.sub i (W64 1)));
            try lia; eauto. }
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
            { rewrite find_f_true;
                [|replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word; eauto].
              apply Hfound. word. }
            eapply transitivity; eauto.
            apply Hsorted with (i:=uint.nat i) (j:=j); try lia; eauto. } }
        { exfalso. apply lookup_lt_Some in Hj_lookup. word. }
  - (* i = 0 — not found *)
    wp_auto. iApply "HΦ". iFrame. iPureIntro.
    split.
    + intros j e Hj_lookup Hj_lt. lia.
    + intros j e Hj_lookup Hj_ge.
      assert (uint.nat i = 0) as Hi0 by word.
      destruct (decide (sint.Z i < sint.Z sl.(slice.len_f))).
      { assert (find_f R key items_list (sint.Z i) = true) as Hfi
          by (apply Hfound; word).
        destruct (decide (j = 0)).
        { subst. rewrite /f /find_f in Hfi.
          replace (Z.to_nat (sint.Z i)) with 0%nat in Hfi by word.
          rewrite Hj_lookup in Hfi.
          apply bool_decide_eq_true in Hfi. done. }
        { list_elem items_list 0 as x0.
          assert (R key x0).
          { rewrite find_f_true;
              [|replace (Z.to_nat (sint.Z i)) with 0%nat by word; eauto].
            apply Hfound. word. }
          eapply transitivity; eauto.
          apply Hsorted with (i:=0%nat) (j:=j); try lia; eauto. } }
      { exfalso. apply lookup_lt_Some in Hj_lookup. word. }
  *)
Admitted.

End proof.
