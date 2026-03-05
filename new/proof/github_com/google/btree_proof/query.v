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

(** ** min *)

Lemma wp_min enforce_min height R
    (n : loc) (elems : gset interface.t) (degree : Z) :
  {{{ is_pkg_init btree ∗
      node_repr_aux enforce_min height R n elems degree ∗
      ⌜n ≠ null⌝ }}}
    (FuncResolve btree.min [] #()) #n
  {{{ (result : interface.t), RET #result;
      node_repr_aux enforce_min height R n elems degree ∗
      ⌜result ≠ interface.nil →
        result ∈ elems ∧ ∀ e, e ∈ elems → ¬R e result⌝ }}}.
Proof.
  (*wp_start as "(Hnode & %Hnn)".
  wp_auto. wp_func_call. wp_call. wp_auto.
  rewrite bool_decide_false //.
  wp_auto.
  (* Loop invariant: cur node's subtree contains the min of elems *)
  iAssert (
    ∃ (cur : loc) (em : bool) (h : nat) (cur_elems : gset interface.t),
      "n" ∷ n_ptr ↦ cur ∗
      "Hcur" ∷ node_repr_aux em h R cur cur_elems degree ∗
      "Hclose" ∷ (node_repr_aux em h R cur cur_elems degree -∗
                   node_repr_aux enforce_min height R n elems degree) ∗
      "%Hmin_pres" ∷ ⌜∀ m, m ∈ elems → (∀ e, e ∈ elems → ¬R e m) →
                        m ∈ cur_elems ∧ (∀ e, e ∈ cur_elems → ¬R e m)⌝
  )%I with "[n Hnode]" as "HI".
  { iExists n, enforce_min, height, elems. iFrame.
    iSplit; [iIntros "$"|]; done. }
  wp_bind (do_for _ _ _). iApply (wp_for with "[-]"). { by iNamedAccu. }
  iIntros "!# __CTX". iNamed "__CTX". iNamed "HI".
  (* Evaluate the for condition: open node_repr_aux to access children *)
  destruct h as [|h']; simpl; iNamed "Hcur";
    iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len;
    iDestruct (own_slice_len with "Hitems_own") as %Hitems_len.
  - (* height 0: leaf — children = [] *)
    iDestruct "Hchildren_rep" as %[Hcl_nil Hcs_nil].
    wp_auto.
    (* condition is false: len(children) = 0 *)
    destruct (decide _) as [Habs|_].
    { exfalso. subst child_locs. simpl in *. word. }
    destruct (decide _) as [_|Habs].
    2:{ exfalso. apply Habs. subst child_locs. simpl in *. done. }
    (* Now at Φ execute_val — this is the post-loop continuation *)
    wp_auto. wp_if_destruct.
    + (* items empty → return nil *)
      iApply "HΦ". iSplitL.
      { iApply "Hclose". iExists items_sl, children_sl, cow_val, items_list, [], [].
        iFrame. iPureIntro. repeat split; try done; try set_solver. }
      iPureIntro. intros Habs'. exfalso. exact (Habs' eq_refl).
    + (* items non-empty → return items[0] *)
      assert (length items_list > 0)%nat as Hitems_pos by word.
      list_elem items_list 0%nat as item0.
      rewrite decide_True; [|word].
      wp_bind (![_] _)%E.
      wp_apply (wp_load_slice_index with "[$Hitems_own]") as "Hitems_own".
      { word. }
      { iPureIntro. exact Hitem0_lookup. }
      iApply "HΦ". iSplitL.
      { iApply "Hclose". iExists items_sl, children_sl, cow_val, items_list, [], [].
        iFrame. iPureIntro. repeat split; try done; try set_solver. }
      iPureIntro. intros Hitem0_nn.
      subst child_locs children_sets.
      rewrite Helems union_empty_r_L.
      split.
      { apply elem_of_list_to_set. eapply list_elem_of_lookup_2. exact Hitem0_lookup. }
      intros e He.
      destruct (Hmin_pres item0) as [_ Hitem0_min].
      { rewrite Helems union_empty_r_L. apply elem_of_list_to_set.
        eapply list_elem_of_lookup_2. exact Hitem0_lookup. }
      { intros e' He'.
        rewrite Helems union_empty_r_L in He'.
        apply elem_of_list_to_set in He'.
        apply list_elem_of_lookup_1 in He' as [j Hj].
        destruct (decide (j = 0%nat)) as [->|].
        - rewrite Hj in Hitem0_lookup. injection Hitem0_lookup as <-.
          intros HR. exact (irreflexivity R _ HR).
        - intros HR.
          exact (irreflexivity R item0 (transitivity HR (Hsorted 0%nat j ltac:(lia) item0 _ Hitem0_lookup Hj))). }
      apply Hitem0_min. rewrite Helems union_empty_r_L.
      apply elem_of_list_to_set.
      apply elem_of_list_to_set in He.
      apply list_elem_of_lookup_1 in He as [j Hj].
      eapply list_elem_of_lookup_2. exact Hj.
  - (* height S h': interior node *)
    wp_auto. wp_if_destruct.
    + (* len(children) > 0, walk to children[0] *)
      assert (length child_locs > 0)%nat as Hcl_pos by word.
      list_elem child_locs 0%nat as child0.
      iDestruct (big_sepL2_length with "Hchildren_rep") as %Hcl_cs_len.
      assert (∃ cs0, children_sets !! 0%nat = Some cs0) as [cs0 Hcs0]
        by (apply lookup_lt_is_Some_2; lia).
      rewrite decide_True; [|word].
      wp_bind (![_] _)%E.
      wp_apply (wp_load_slice_index with "[$Hchildren_own]") as "Hchildren_own".
      { word. }
      { iPureIntro. exact Hchild0_lookup. }
      iDestruct (big_sepL2_lookup_acc with "Hchildren_rep") as "[Hchild Hchildren_rep_close]".
      { exact Hchild0_lookup. }
      { exact Hcs0. }
      wp_auto.
      wp_for_post.
      iExists child0, true, h', cs0.
      iFrame "n Hchild".
      iSplit.
      { iIntros "Hchild".
        iDestruct ("Hchildren_rep_close" with "Hchild") as "Hchildren_rep".
        iApply "Hclose".
        iExists items_sl, children_sl, cow_val, items_list, child_locs, children_sets.
        iFrame. iPureIntro. repeat split; try done; try apply Hordering. }
      iPureIntro.
      intros m Hm Hmin.
      destruct (Hmin_pres m Hm Hmin) as [Hm_cur Hm_min_cur].
      rewrite Helems in Hm_cur.
      apply elem_of_union in Hm_cur as [Hm_items | Hm_children].
      * (* m ∈ items — contradiction *)
        apply elem_of_list_to_set in Hm_items.
        apply list_elem_of_lookup_1 in Hm_items as [j Hj].
        destruct Hordering as [Hupper Hlower].
        destruct (decide (cs0 = ∅)) as [->|Hne].
        { split; [set_solver|done]. }
        exfalso.
        assert (∃ e, e ∈ cs0) as [e He] by (apply set_choose_L; done).
        assert (e ∈ (list_to_set items_list ∪ ⋃ children_sets)) as He_cur.
        { apply elem_of_union_r. apply elem_of_union_list.
          eexists. split; [eapply list_elem_of_lookup_2; exact Hcs0|done]. }
        rewrite -Helems in He_cur.
        assert (¬R e m) as HneR by (apply Hm_min_cur; done).
        assert (j < length items_list)%nat as Hj_bound by (eapply lookup_lt_Some; eauto).
        destruct (decide (j = 0%nat)) as [->|Hj_ne0].
        { exact (HneR (Hupper 0%nat cs0 m Hcs0 Hj e He)). }
        { assert (∃ x0, items_list !! 0%nat = Some x0) as [x0 Hx0]
            by (apply lookup_lt_is_Some_2; lia).
          exact (HneR (transitivity (Hupper 0%nat cs0 x0 Hcs0 Hx0 e He)
                                     (Hsorted 0%nat j ltac:(lia) x0 m Hx0 Hj))). }
      * (* m ∈ ⋃ children_sets *)
        rewrite elem_of_union_list in Hm_children.
        destruct Hm_children as [s [Hs_in Hm_in_s]].
        apply list_elem_of_lookup_1 in Hs_in as [k Hk].
        destruct Hordering as [Hupper Hlower].
        destruct (decide (k = 0%nat)) as [->|Hk_ne0].
        { rewrite Hk in Hcs0. injection Hcs0 as <-.
          split; [done|].
          intros e He_cs0. apply Hm_min_cur.
          rewrite Helems. apply elem_of_union_r. apply elem_of_union_list.
          eexists. split; [eapply list_elem_of_lookup_2; exact Hcs0|done]. }
        { exfalso.
          assert (0 < k)%nat as Hk_pos by lia.
          assert (k - 1 < length items_list)%nat.
          { assert (k < length children_sets)%nat by (eapply lookup_lt_Some; eauto). lia. }
          assert (∃ xk1, items_list !! (k - 1)%nat = Some xk1) as [xk1 Hxk1]
            by (apply lookup_lt_is_Some_2; lia).
          assert (R xk1 m) by exact (Hlower k s xk1 Hk_pos Hk Hxk1 m Hm_in_s).
          assert (xk1 ∈ (list_to_set items_list ∪ ⋃ children_sets)).
          { apply elem_of_union_l. apply elem_of_list_to_set.
            eapply list_elem_of_lookup_2. exact Hxk1. }
          rewrite -Helems in *.
          exact (Hm_min_cur xk1 ltac:(done) ltac:(done)). }
    + (* Loop exit: len(children) = 0 *)
      assert (child_locs = []) as Hcl_nil by (apply nil_length_inv; word).
      iDestruct (big_sepL2_nil_inv_l with "Hchildren_rep") as %Hcs_nil.
      { exact Hcl_nil. }
      wp_auto. wp_if_destruct.
      * (* items empty → return nil *)
        iApply "HΦ". iSplitL.
        { iApply "Hclose". subst child_locs children_sets.
          iExists items_sl, children_sl, cow_val, items_list, [], [].
          iFrame. iSplit; [done|]. iPureIntro. repeat split; try done; try apply Hordering. }
        iPureIntro. intros Habs. exfalso. exact (Habs eq_refl).
      * (* items non-empty → return items[0] *)
        assert (length items_list > 0)%nat as Hitems_pos by word.
        list_elem items_list 0%nat as item0.
        rewrite decide_True; [|word].
        wp_bind (![_] _)%E.
        wp_apply (wp_load_slice_index with "[$Hitems_own]") as "Hitems_own".
        { word. }
        { iPureIntro. exact Hitem0_lookup. }
        iApply "HΦ". iSplitL.
        { iApply "Hclose". subst child_locs children_sets.
          iExists items_sl, children_sl, cow_val, items_list, [], [].
          iFrame. iSplit; [done|]. iPureIntro. repeat split; try done; try apply Hordering. }
        iPureIntro. intros Hitem0_nn.
        subst child_locs children_sets.
        rewrite Helems union_empty_r_L.
        destruct (Hmin_pres item0) as [Hitem0_in Hitem0_min].
        { rewrite Helems union_empty_r_L. apply elem_of_list_to_set.
          eapply list_elem_of_lookup_2. exact Hitem0_lookup. }
        { intros e He.
          rewrite Helems union_empty_r_L in He.
          apply elem_of_list_to_set in He.
          apply list_elem_of_lookup_1 in He as [j Hj].
          destruct (decide (j = 0%nat)) as [->|].
          - rewrite Hj in Hitem0_lookup. injection Hitem0_lookup as <-.
            intros HR. exact (irreflexivity R _ HR).
          - intros HR.
            exact (irreflexivity R item0 (transitivity HR (Hsorted 0%nat j ltac:(lia) item0 _ Hitem0_lookup Hj))). }
        split.
        { apply elem_of_list_to_set. eapply list_elem_of_lookup_2. exact Hitem0_lookup. }
        intros e He.
        apply elem_of_list_to_set in He.
        apply list_elem_of_lookup_1 in He as [j Hj].
        destruct (decide (j = 0%nat)) as [->|Hj_ne0].
        { rewrite Hj in Hitem0_lookup. injection Hitem0_lookup as <-.
          intros HR. exact (irreflexivity R _ HR). }
        { intros HR.
          assert (R item0 e) as H0j by (eapply Hsorted; [lia | exact Hitem0_lookup | exact Hj]).
          exact (irreflexivity R item0 (transitivity HR H0j)). }*)
Admitted.

End proof.
