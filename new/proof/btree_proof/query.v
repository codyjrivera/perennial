From New.generatedproof Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.btree_proof Require Import btree_init rep items.

(** * Read-only btree operations: Get, Has, Len, Min, Max. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx: GoContext}.

(** ** Len *)

Lemma wp_BTree__Len R (t : loc) (elems : gset interface.t) :
  {{{ is_pkg_init btree ∗ btree_repr R t elems }}}
    t @ (ptrT.id btree.BTree.id) @ "Len"%go #()
  {{{ (n : w64), RET #n;
      btree_repr R t elems ∗
      ⌜uint.Z n = Z.of_nat (size elems)⌝ }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  iApply "HΦ".
  iFrame. iPureIntro. done.
Qed.

(** ** node.get

    STATUS (2026-02-19):
    - Using [iLöb] for recursive spec.
    - [wp_auto] handles allocs. [wp_apply wp_items__find] works inside
      [exception_do]. [wp_if_destruct] works for [found] and [len(children)].
    - STUCK on "found = true" branch: need to load [items[idx]] but
      [wp_pure] and [wp_load_slice_elem'] both fail — [walk_expr] doesn't
      seem to traverse [exception_seq]/[do_return] contexts.
    - "found = false, leaf, return nil" branch: postcondition proof works
      (using [Hfind_below]/[Hfind_above] from items.find).
    - "found = false, children > 0" recursive branch: not started.
    - "found = false, no children, S h" branch: postcondition needs
      argument that all elements in children_sets satisfy R e key ∨ R key e.
*)

Lemma wp_node__get enforce_min height R
    `{!RelDecision R, !Transitive R}
    (n : loc) (elems : gset interface.t)
    (degree : Z) (key : interface.t) :
  {{{ is_pkg_init btree ∗
      node_repr_aux enforce_min height R n elems degree ∗
      is_less_order R ∗
      ⌜key ≠ interface.nil⌝ }}}
    n @ (ptrT.id btree.node.id) @ "get"%go #key
  {{{ (result : interface.t), RET #result;
      node_repr_aux enforce_min height R n elems degree ∗
      ⌜(result ≠ interface.nil → result ∈ elems ∧ ¬R result key ∧ ¬R key result) ∧
       (result = interface.nil → ∀ e, e ∈ elems → R e key ∨ R key e)⌝ }}}.
Proof.
  iLöb as "IH" forall (enforce_min height n elems).
  wp_start as "(Hnode & #Hless & %Hkey_nn)".
  destruct height as [|h]; simpl; iNamed "Hnode";
    iDestruct (own_slice_len with "Hitems_own") as %Hitems_len.
  - (* height = 0: leaf *)
    iDestruct "Hchildren_rep" as %[Hcl_nil Hcs_nil].
    wp_auto.
    wp_apply (wp_items__find with "[$Hitems_own $Hless]").
    { iFrame "%". }
    iIntros (idx found) "(Hitems_own & %Hfind)".
    wp_auto.
    wp_if_destruct.
    + (* found = true: return items[idx] *)
      destruct Hfind as (e & Hlookup & Hne & Hnk).
      assert (0 ≤ sint.Z idx < sint.Z items_sl.(slice.len_f)) as Hidx_bound.
      { apply lookup_lt_Some in Hlookup. word. }
      wp_bind (load_ty _ _).
      wp_auto.
      wp_apply (wp_load_slice_elem with "[$Hitems_own]") as "Hitems_own".
      { word. }
      { iPureIntro. replace (sint.nat idx) with (uint.nat idx) by word. exact Hlookup. }
      (* After wp_bind + load, continuation is WP exception_do ((return: #e) ;;; ...) *)
      (* which wp_auto should resolve, but if goal is already Φ, skip *)
      iApply "HΦ".
      iSplitL.
      { subst.
        iExists items_sl, children_sl, items, [], [].
        iFrame "Hitems_field Hchildren_field Hitems_own Hchildren_own".
        iPureIntro. repeat split; try done; try set_solver. }
      iPureIntro. split.
      { intros _. split; [|split]; eauto.
        subst elems. apply elem_of_union_l.
        apply elem_of_list_to_set. eapply list_elem_of_lookup_2. exact Hlookup. }
      { intros Habs. exfalso.
        assert (e ≠ interface.nil).
        { exact (Forall_lookup_1 _ _ _ _ Hitems_non_nil Hlookup). }
        congruence. }
    + (* found = false, leaf *)
      destruct Hfind as (Hidx_le & Hfind_below & Hfind_above).
      wp_if_destruct.
      * (* len(children) > 0 — contradiction: leaf has [] children *)
        iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len.
        exfalso. simpl in *. word.
      * (* leaf, return nil *)
        iApply "HΦ".
        iSplitL.
        { iExists items_sl, children_sl, items, [], [].
          iFrame. iPureIntro.
          repeat split; try done; try set_solver. }
        iPureIntro. split.
        { intros Habs. exfalso. exact (Habs eq_refl). }
        { intros _ e He.
          rewrite union_empty_r_L in He.
          apply elem_of_list_to_set in He.
          apply list_elem_of_lookup_1 in He as [j Hj].
          destruct (decide (j < uint.nat idx)%nat).
          - left. eapply Hfind_below; eauto.
          - right. eapply Hfind_above; eauto. lia. }
  - (* height = S h *)
    wp_auto.
    wp_apply (wp_items__find with "[$Hitems_own $Hless]").
    { iFrame "%". }
    iIntros (idx found) "(Hitems_own & %Hfind)".
    wp_auto.
    wp_if_destruct.
    + (* found = true: return items[idx] *)
      destruct Hfind as (e & Hlookup & Hne & Hnk).
      assert (0 ≤ sint.Z idx < sint.Z items_sl.(slice.len_f)) as Hidx_bound.
      { apply lookup_lt_Some in Hlookup. word. }
      wp_bind (load_ty _ _).
      wp_auto.
      wp_apply (wp_load_slice_elem with "[$Hitems_own]") as "Hitems_own".
      { word. }
      { iPureIntro. replace (sint.nat idx) with (uint.nat idx) by word. exact Hlookup. }
      iApply "HΦ".
      iSplitL.
      { iExists items_sl, children_sl, items, child_locs, children_sets.
        iFrame "Hitems_field Hchildren_field Hitems_own Hchildren_own Hchildren_rep".
        iPureIntro. repeat split; try done; try apply Hordering. }
      iPureIntro. split.
      { intros _. split; [|split]; eauto.
        subst elems. apply elem_of_union_l.
        apply elem_of_list_to_set. eapply list_elem_of_lookup_2. exact Hlookup. }
      { intros Habs. exfalso.
        exact (Forall_lookup_1 _ _ _ _ Hitems_non_nil Hlookup Habs). }
    + (* found = false *)
      destruct Hfind as (Hidx_le & Hfind_below & Hfind_above).
      wp_if_destruct.
      * (* len(children) > 0 — recurse into children[idx].
           Steps needed:
           (1) Load children[idx] via wp_load_slice_elem on Hchildren_own.
           (2) Extract idx-th child from [∗ list] Hchildren_rep
               (big_sepL2_lookup_acc or similar).
           (3) wp_apply "IH" with the child's node_repr_aux.
           (4) Reassemble [∗ list] (put child back).
           (5) Postcondition for result=nil: btree_ordering + transitivity. *)
        iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len.
        (* child_locs = items + 1 (from Hsize + children > 0) *)
        assert (length child_locs = (length items + 1)%nat) as Hcl_items.
        { assert (length child_locs > 0)%nat by word.
          destruct enforce_min; [destruct Hsize as [[? _]|[? _]]|destruct Hsize as [[?|?] _]]; lia. }
        (* idx < len(child_locs) because idx ≤ len(items) from items.find *)
        assert (uint.nat idx < length child_locs) as Hidx_child_bound by lia.
        assert (0 ≤ sint.Z idx < sint.Z children_sl.(slice.len_f)) as Hidx_cbound.
        { word. }
        list_elem child_locs (uint.nat idx) as child_loc.
        (* Also need the corresponding child set *)
        iDestruct (big_sepL2_length with "Hchildren_rep") as %Hcl_cs_len.
        assert (∃ child_set, children_sets !! uint.nat idx = Some child_set)
          as [child_set Hcs_lookup].
        { apply lookup_lt_is_Some_2. lia. }
        (* Load children[idx] *)
        wp_bind (load_ty _ _).
        wp_auto.
        wp_apply (wp_load_slice_elem with "[$Hchildren_own]") as "Hchildren_own".
        { word. }
        { iPureIntro. replace (sint.nat idx) with (uint.nat idx) by word.
          exact Hchild_loc_lookup. }
        (* Extract child from big_sepL2 *)
        iDestruct (big_sepL2_lookup_acc with "Hchildren_rep") as "[Hchild Hchildren_rep_close]".
        { exact Hchild_loc_lookup. }
        { exact Hcs_lookup. }
        (* Recursive call *)
        wp_apply ("IH" with "[Hchild]").
        { iFrame "Hchild Hless". iFrame "#". iPureIntro. exact Hkey_nn. }
        iIntros (result) "(Hchild & %Hresult)".
        (* Put child back *)
        iDestruct ("Hchildren_rep_close" with "Hchild") as "Hchildren_rep".
        (* Now prove postcondition *)
        wp_auto.
        iApply "HΦ".
        iSplitL.
        { iExists items_sl, children_sl, items, child_locs, children_sets.
          iFrame "Hitems_field Hchildren_field Hitems_own Hchildren_own Hchildren_rep".
          iPureIntro. repeat split; try done; try apply Hordering. }
        iPureIntro.
        destruct Hresult as [Hresult_found Hresult_nil].
        split.
        { (* result ≠ nil → result ∈ elems ∧ ¬R result key ∧ ¬R key result
             From IH: result ∈ child_set. child_set ∈ children_sets (via Hcs_lookup).
             So result ∈ ⋃ children_sets ⊆ elems. *)
          intros Hnn. destruct (Hresult_found Hnn) as (Hin & Hr1 & Hr2).
          split; [|split]; eauto.
          apply elem_of_union_r. apply elem_of_union_list.
          exists child_set. split; eauto.
          apply list_elem_of_lookup_2 with (i := uint.nat idx). exact Hcs_lookup. }
        { (* result = nil → ∀ e ∈ elems, R e key ∨ R key e *)
          intros Hnil e He.
          apply elem_of_union in He as [He | He].
          { (* e ∈ list_to_set items *)
            apply elem_of_list_to_set in He.
            apply list_elem_of_lookup_1 in He as [j Hj].
            destruct (decide (j < uint.nat idx)%nat).
            - left. eapply Hfind_below; eauto.
            - right. eapply Hfind_above; eauto. lia. }
          { (* e ∈ ⋃ children_sets *)
            rewrite elem_of_union_list in He.
            destruct He as (s & Hs_mem & He_in_s).
            apply list_elem_of_lookup_1 in Hs_mem as [k Hk].
            destruct Hordering as [Hupper Hlower].
            destruct (decide (k < uint.nat idx)%nat).
            - (* k < idx: upper bound + transitivity → R e key *)
              left.
              assert (∃ x_k, items !! k = Some x_k) as [x_k Hx_k]
                by (apply lookup_lt_is_Some_2; lia).
              eapply transitivity.
              + exact (Hupper k s x_k Hk Hx_k e He_in_s).
              + eapply Hfind_below; eauto.
            - destruct (decide (k = uint.nat idx)).
              + (* k = idx: from IH *)
                subst k. rewrite Hk in Hcs_lookup. injection Hcs_lookup as <-.
                exact (Hresult_nil Hnil e He_in_s).
              + (* k > idx: lower bound + transitivity → R key e *)
                right.
                assert (k - 1 < length items)%nat.
                { assert (k < length children_sets)%nat by (eapply lookup_lt_Some; eauto).
                  lia. }
                assert (∃ x_k1, items !! (k - 1)%nat = Some x_k1) as [x_k1 Hx_k1]
                  by (apply lookup_lt_is_Some_2; lia).
                eapply transitivity.
                * eapply Hfind_above; eauto. lia.
                * exact (Hlower k s x_k1 ltac:(lia) Hk Hx_k1 e He_in_s). } }
      * (* no children, return nil.
           Postcondition: show ∀ e ∈ elems, R e key ∨ R key e.
           Items: same as leaf case via Hfind_below/Hfind_above.
           Children: need to show all e in ⋃ children_sets satisfy it,
           but if no children (len=0), children_sets might still be nonempty
           at height S h — need to argue from Hsize or similar. *)
        (* children_sl has length 0, so child_locs = [] *)
        iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len.
        assert (child_locs = []) as Hcl_nil.
        { apply nil_length_inv. word. }
        subst child_locs.
        iDestruct (big_sepL2_nil_inv_l with "Hchildren_rep") as %Hcs_nil.
        subst children_sets.
        iApply "HΦ".
        iSplitL.
        { iExists items_sl, children_sl, items, [], [].
          iFrame "Hitems_field Hchildren_field Hitems_own Hchildren_own".
          iSplit. { done. }
          iPureIntro. repeat split; try done; try apply Hordering. }
        iPureIntro. split.
        { intros Habs. exfalso. exact (Habs eq_refl). }
        { intros _ e He.
          rewrite union_empty_r_L in He.
          apply elem_of_list_to_set in He.
          apply list_elem_of_lookup_1 in He as [j Hj].
          destruct (decide (j < uint.nat idx)%nat).
          - left. eapply Hfind_below; eauto.
          - right. eapply Hfind_above; eauto. lia. }
Qed.

(** ** BTree.Get *)

Lemma wp_BTree__Get R `{!RelDecision R, !Transitive R}
    (t : loc) (elems : gset interface.t)
    (key : interface.t) :
  {{{ is_pkg_init btree ∗
      btree_repr R t elems ∗
      is_less_order R ∗
      ⌜key ≠ interface.nil⌝ }}}
    t @ (ptrT.id btree.BTree.id) @ "Get"%go #key
  {{{ (result : interface.t), RET #result;
      btree_repr R t elems ∗
      ⌜(result ≠ interface.nil → result ∈ elems ∧ ¬R result key ∧ ¬R key result) ∧
       (result = interface.nil → ∀ e, e ∈ elems → R e key ∨ R key e)⌝ }}}.
Proof.
  wp_start as "(Hbtree & #Hless & %Hkey_nn)".
  iNamed "Hbtree".
  wp_auto.
  wp_if_destruct.
  - (* root = null → return nil *)
    iDestruct "Hroot" as %Hempty.
    iApply "HΦ".
    iSplitL.
    { iExists degree_val, len_val, null, cow_loc.
      iFrame. done. }
    iPureIntro. split.
    + intros Habs. exfalso. exact (Habs eq_refl).
    + intros _ e He. subst elems. set_solver.
  - (* root ≠ null → call node__get *)
    iAssert (∃ height, node_repr height R root_loc elems (uint.Z degree_val))%I
      with "[Hroot]" as (height) "Hroot".
    { destruct (decide (root_loc = null)); [contradiction|iFrame]. }
    wp_apply (wp_node__get with "[$Hroot $Hless]").
    { iFrame "#". iPureIntro. exact Hkey_nn. }
    iIntros (result) "(Hroot & %Hresult)".
    wp_auto.
    iApply "HΦ".
    iSplitL.
    { iExists degree_val, len_val, root_loc, cow_loc.
      iFrame "∗ %".
      destruct (decide (root_loc = null)); [contradiction|].
      iExists height. iFrame. }
    iPureIntro. exact Hresult.
Qed.

(** ** BTree.Has *)

Lemma wp_BTree__Has R `{!RelDecision R, !Transitive R}
    (t : loc) (elems : gset interface.t)
    (key : interface.t) :
  {{{ is_pkg_init btree ∗
      btree_repr R t elems ∗
      is_less_order R ∗
      ⌜key ≠ interface.nil⌝ }}}
    t @ (ptrT.id btree.BTree.id) @ "Has"%go #key
  {{{ (b : bool), RET #b;
      btree_repr R t elems ∗
      ⌜b ↔ ∃ e, e ∈ elems ∧ ¬R e key ∧ ¬R key e⌝ }}}.
Proof.
  wp_start as "(Hbtree & #Hless & %Hkey_nn)".
  wp_auto.
  wp_apply (wp_BTree__Get with "[$Hbtree $Hless]").
  { iPureIntro. exact Hkey_nn. }
  iIntros (result) "(Hbtree & %Hresult)".
  destruct Hresult as [Hresult_found Hresult_nil].
  wp_auto.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  destruct (decide (result = interface.nil)) as [Hnil|Hnn].
  - (* result = nil → b = false *)
    rewrite Hnil. rewrite bool_decide_eq_true_2; [|done]. simpl.
    split.
    + intros [].
    + intros (e & He & HnR1 & HnR2).
      destruct (Hresult_nil Hnil e He); contradiction.
  - (* result ≠ nil → b = true *)
    rewrite bool_decide_eq_false_2; [|done]. simpl.
    destruct (Hresult_found Hnn) as (Hin & HnR1 & HnR2).
    split.
    + intros _. exists result. eauto.
    + intros _. done.
Qed.

End proof.
