From New.generatedproof.github_com.google Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.github_com.google.btree_proof Require Import btree_init rep items.

(** * Read-only btree operations: Get, Has, Len. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : btree.Assumptions}.
Collection W := sem + package_sem.

Set Default Proof Using "All".

(** ** Len *)

Lemma wp_BTree__Len R (t : loc) (elems : gset interface.t) :
  {{{ is_pkg_init btree ∗ btree_repr R t elems }}}
    t @! (go.PointerType (btree.BTree)) @! "Len" #()
  {{{ (n : w64), RET #n;
      btree_repr R t elems ∗
      ⌜uint.Z n = Z.of_nat (size elems)⌝ }}}.
Proof.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  iApply "HΦ". iFrame. iPureIntro. done.
Qed.

(** ** node.get *)

Lemma wp_node__get enforce_min height R
    `{!RelDecision R, !Transitive R}
    (n : loc) (elems : gset interface.t)
    (degree : Z) (key : interface.t) :
  {{{ is_pkg_init btree ∗
      node_repr_aux enforce_min height R n elems degree ∗
      is_less_fn R ∗
      ⌜key ≠ interface.nil⌝ }}}
    n @! (go.PointerType (btree.node)) @! "get" #key
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
    wp_bind ((n.[btree.node.t, "items"]) @! (go.PointerType btree.items) @! "find" (#key))%E.
    wp_method_call. wp_call.
    wp_auto.
    wp_apply (wp_items__find with "[$Hitems_own $Hless]").
    { iFrame "%". }
    iIntros (idx found) "(Hitems_own & %Hfind)".
    wp_auto.
    wp_if_destruct.
    + (* found = true: return items[idx] *)
      destruct Hfind as (e & Hlookup & Hne & Hnk).
      assert (0 ≤ sint.Z idx < sint.Z items_sl.(slice.len)) as Hidx_bound.
      { apply lookup_lt_Some in Hlookup. word. }
      rewrite decide_True //.
      wp_bind (![_] _)%E.
      wp_apply (wp_load_slice_index with "[$Hitems_own]") as "Hitems_own".
      { word. }
      { iPureIntro. replace (Z.to_nat (sint.Z idx)) with (uint.nat idx) by word. exact Hlookup. }
      subst child_locs children_sets.
      iApply "HΦ".
      iSplitL.
      { iExists items_sl, children_sl, cow_val, items_list, [], [].
        iFrame "Hitems Hchildren Hcow Hitems_own Hchildren_own".
        iPureIntro. repeat split; try done; try set_solver. }
      iPureIntro. split.
      { intros _. split; [|split]; eauto.
        subst elems. apply elem_of_union_l.
        apply elem_of_list_to_set. eapply list_elem_of_lookup_2. exact Hlookup. }
      { intros Habs. exfalso.
        exact (Forall_lookup_1 _ _ _ _ Hitems_non_nil Hlookup Habs). }
    + (* found = false, leaf *)
      destruct Hfind as (Hidx_le & Hfind_below & Hfind_above).
      wp_if_destruct.
      * (* len(children) > 0 — contradiction: leaf has [] children *)
        iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len.
        exfalso. simpl in *. word.
      * (* leaf, return nil *)
        iApply "HΦ".
        iSplitL.
        { iExists items_sl, children_sl, cow_val, items_list, [], [].
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
    wp_bind ((n.[btree.node.t, "items"]) @! (go.PointerType btree.items) @! "find" (#key))%E.
    wp_method_call. wp_call.
    wp_auto.
    wp_apply (wp_items__find with "[$Hitems_own $Hless]").
    { iFrame "%". }
    iIntros (idx found) "(Hitems_own & %Hfind)".
    wp_auto.
    wp_if_destruct.
    + (* found = true: return items[idx] *)
      destruct Hfind as (e & Hlookup & Hne & Hnk).
      assert (0 ≤ sint.Z idx < sint.Z items_sl.(slice.len)) as Hidx_bound.
      { apply lookup_lt_Some in Hlookup. word. }
      rewrite decide_True //.
      wp_bind (![_] _)%E.
      wp_apply (wp_load_slice_index with "[$Hitems_own]") as "Hitems_own".
      { word. }
      { iPureIntro. replace (Z.to_nat (sint.Z idx)) with (uint.nat idx) by word. exact Hlookup. }
      iApply "HΦ".
      iSplitL.
      { iExists items_sl, children_sl, cow_val, items_list, child_locs, children_sets.
        iFrame "Hitems Hchildren Hcow Hitems_own Hchildren_own Hchildren_rep".
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
      * (* len(children) > 0 — recurse into children[idx] *)
        iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len.
        assert (length child_locs = (length items_list + 1)%nat) as Hcl_items.
        { assert (length child_locs > 0)%nat by word.
          destruct enforce_min; [destruct Hsize as [[? _]|[? _]]|destruct Hsize as [[?|?] _]]; lia. }
        assert (uint.nat idx < length child_locs) as Hidx_child_bound by lia.
        assert (0 ≤ sint.Z idx < sint.Z children_sl.(slice.len)) as Hidx_cbound.
        { word. }
        list_elem child_locs (uint.nat idx) as child_loc.
        iDestruct (big_sepL2_length with "Hchildren_rep") as %Hcl_cs_len.
        assert (∃ child_set, children_sets !! uint.nat idx = Some child_set)
          as [child_set Hcs_lookup].
        { apply lookup_lt_is_Some_2. lia. }
        rewrite decide_True; [|word].
        (* Load children[idx] *)
        wp_bind (![_] _)%E.
        wp_apply (wp_load_slice_index with "[$Hchildren_own]") as "Hchildren_own".
        { word. }
        { iPureIntro. replace (Z.to_nat (sint.Z idx)) with (uint.nat idx) by word.
          exact Hchild_loc_lookup. }
        (* Extract child from big_sepL2 *)
        iDestruct (big_sepL2_lookup_acc with "Hchildren_rep") as "[Hchild Hchildren_rep_close]".
        { exact Hchild_loc_lookup. }
        { exact Hcs_lookup. }
        (* Recursive call *)
        wp_apply ("IH" with "[Hchild]").
        { iFrame "Hchild Hless". iFrame "#". iPureIntro. exact Hkey_nn. }
        iIntros (result) "(Hchild & %Hresult)".
        iDestruct ("Hchildren_rep_close" with "Hchild") as "Hchildren_rep".
        wp_auto.
        iApply "HΦ".
        iSplitL.
        { iExists items_sl, children_sl, cow_val, items_list, child_locs, children_sets.
          iFrame "Hitems Hchildren Hcow Hitems_own Hchildren_own Hchildren_rep".
          iPureIntro. repeat split; try done; try apply Hordering. }
        iPureIntro.
        destruct Hresult as [Hresult_found Hresult_nil].
        split.
        { intros Hnn. destruct (Hresult_found Hnn) as (Hin & Hr1 & Hr2).
          split; [|split]; eauto.
          apply elem_of_union_r. apply elem_of_union_list.
          exists child_set. split; eauto.
          apply list_elem_of_lookup_2 with (i := uint.nat idx). exact Hcs_lookup. }
        { intros Hnil e He.
          apply elem_of_union in He as [He | He].
          { apply elem_of_list_to_set in He.
            apply list_elem_of_lookup_1 in He as [j Hj].
            destruct (decide (j < uint.nat idx)%nat).
            - left. eapply Hfind_below; eauto.
            - right. eapply Hfind_above; eauto. lia. }
          { rewrite elem_of_union_list in He.
            destruct He as (s & Hs_mem & He_in_s).
            apply list_elem_of_lookup_1 in Hs_mem as [k Hk].
            destruct Hordering as [Hupper Hlower].
            destruct (decide (k < uint.nat idx)%nat).
            - left.
              assert (∃ x_k, items_list !! k = Some x_k) as [x_k Hx_k]
                by (apply lookup_lt_is_Some_2; lia).
              eapply transitivity.
              + exact (Hupper k s x_k Hk Hx_k e He_in_s).
              + eapply Hfind_below; eauto.
            - destruct (decide (k = uint.nat idx)).
              + subst k. rewrite Hk in Hcs_lookup. injection Hcs_lookup as <-.
                exact (Hresult_nil Hnil e He_in_s).
              + right.
                assert (k - 1 < length items_list)%nat.
                { assert (k < length children_sets)%nat by (eapply lookup_lt_Some; eauto).
                  lia. }
                assert (∃ x_k1, items_list !! (k - 1)%nat = Some x_k1) as [x_k1 Hx_k1]
                  by (apply lookup_lt_is_Some_2; lia).
                eapply transitivity.
                * eapply Hfind_above; eauto. lia.
                * exact (Hlower k s x_k1 ltac:(lia) Hk Hx_k1 e He_in_s). } }
      * (* no children, return nil *)
        iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len.
        assert (child_locs = []) as Hcl_nil.
        { apply nil_length_inv. word. }
        subst child_locs.
        iDestruct (big_sepL2_nil_inv_l with "Hchildren_rep") as %Hcs_nil.
        subst children_sets.
        iApply "HΦ".
        iSplitL.
        { iExists items_sl, children_sl, cow_val, items_list, [], [].
          iFrame "Hitems Hchildren Hcow Hitems_own Hchildren_own".
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
      is_less_fn R ∗
      ⌜key ≠ interface.nil⌝ }}}
    t @! (go.PointerType (btree.BTree)) @! "Get" #key
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
    { iExists degree_val, length_val, null, cow_val.
      iFrame. done. }
    iPureIntro. split.
    + intros Habs. exfalso. exact (Habs eq_refl).
    + intros _ e He. subst elems. set_solver.
  - (* root ≠ null → call node__get *)
    iAssert (∃ height, node_repr height R root_val elems (uint.Z degree_val))%I
      with "[Hroot]" as (height) "Hroot".
    { destruct (decide (root_val = null)); [contradiction|iFrame]. }
    wp_apply (wp_node__get with "[$Hroot $Hless]").
    { iFrame "#". iPureIntro. exact Hkey_nn. }
    iIntros (result) "(Hroot & %Hresult)".
    wp_auto.
    iApply "HΦ".
    iSplitL.
    { iExists degree_val, length_val, root_val, cow_val.
      iFrame "∗ %".
      destruct (decide (root_val = null)); [contradiction|].
      iExists height. iFrame. }
    iPureIntro. exact Hresult.
Qed.

(** ** BTree.Has *)

Lemma wp_BTree__Has R `{!RelDecision R, !Transitive R}
    (t : loc) (elems : gset interface.t)
    (key : interface.t) :
  {{{ is_pkg_init btree ∗
      btree_repr R t elems ∗
      is_less_fn R ∗
      ⌜key ≠ interface.nil⌝ }}}
    t @! (go.PointerType (btree.BTree)) @! "Has" #key
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
  destruct (decide (result = interface.nil)) as [Hnil|Hnn].
  - subst result. wp_auto. iApply "HΦ". iFrame.
    iPureIntro. split.
    + intros [].
    + intros (e & He & HnR1 & HnR2).
      destruct (Hresult_nil eq_refl e He); contradiction.
  - destruct result as [i|]; [|contradiction]. wp_auto.
    destruct (Hresult_found ltac:(discriminate)) as (Hin & HnR1 & HnR2).
    iApply "HΦ". iFrame.
    iPureIntro. split.
    + intros _. exists (interface.ok i). eauto.
    + intros _. done.
Qed.

End proof.
