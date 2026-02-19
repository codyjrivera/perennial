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
      (* STUCK: need to load items[idx] inside exception_do + exception_seq.
         wp_pure fails ("Cannot find witness").
         wp_load_slice_elem' fails ("iApply: cannot apply").
         walk_expr doesn't traverse exception_seq/do_return contexts. *)
      admit.
    + (* found = false, leaf *)
      destruct Hfind as [Hfind_below Hfind_above].
      wp_if_destruct.
      * (* len(children) > 0 — contradiction: leaf has [] children *)
        iDestruct (own_slice_len with "Hchildren_own") as %Hcl_len.
        exfalso. simpl in *. word.
      * (* leaf, return nil — wp_auto resolves exception_do (return: #nil) *)
        (* Postcondition: reassemble node_repr_aux, then show
           ∀ e ∈ list_to_set items, R e key ∨ R key e
           using Hfind_below (j < idx → R items[j] key)
           and Hfind_above (j ≥ idx → R key items[j]). *)
        admit.
  - (* height = S h *)
    wp_auto.
    wp_apply (wp_items__find with "[$Hitems_own $Hless]").
    { iFrame "%". }
    iIntros (idx found) "(Hitems_own & %Hfind)".
    wp_auto.
    wp_if_destruct.
    + (* found = true: same STUCK issue as height=0 *)
      destruct Hfind as (e & Hlookup & Hne & Hnk).
      admit.
    + (* found = false *)
      destruct Hfind as [Hfind_below Hfind_above].
      wp_if_destruct.
      * (* len(children) > 0 — recurse into children[idx].
           Steps needed:
           (1) Load children[idx] via wp_load_slice_elem on Hchildren_own.
           (2) Extract idx-th child from [∗ list] Hchildren_rep
               (big_sepL2_lookup_acc or similar).
           (3) wp_apply "IH" with the child's node_repr_aux.
           (4) Reassemble [∗ list] (put child back).
           (5) Postcondition for result=nil: btree_ordering + transitivity. *)
        admit.
      * (* no children, return nil.
           Postcondition: show ∀ e ∈ elems, R e key ∨ R key e.
           Items: same as leaf case via Hfind_below/Hfind_above.
           Children: need to show all e in ⋃ children_sets satisfy it,
           but if no children (len=0), children_sets might still be nonempty
           at height S h — need to argue from Hsize or similar. *)
        admit.
Admitted.

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
Proof. Admitted.

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
Proof. Admitted.

End proof.
