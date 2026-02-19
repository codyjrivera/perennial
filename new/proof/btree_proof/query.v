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

    Proof is by induction on [height] (the fuel in [node_repr_aux]).
    At each node:
    1. Call [items.find] to locate [key] in [items].
    2. If found, return the matching item.
    3. If not found and children exist, recurse into [children[idx]].
    4. If not found and no children (leaf), return [nil].

    The "not found + nil from child" postcondition (every element in the
    subtree is R-comparable to key) relies on:
    - [items.find] postcondition for items
    - The IH for [children_sets[idx]]
    - [btree_ordering] upper bounds + transitivity for [j < idx]
    - [btree_ordering] lower bounds + transitivity for [j > idx]

    STATUS (2026-02-18):
    - Induction structure: [revert enforce_min n elems; induction height].
    - wp_start + wp_auto + wp_apply wp_items__find + wp_if_destruct all work.
    - "found = true" branches (both heights):
        wp_load_slice_elem fires to load items[idx].
        UNTESTED whether wp_auto after the load steps through
        return:/exception_seq/exception_do. The postcondition proof:
        elem ∈ elems via Helems + elem_of_list_to_set + Helem_lookup.
        elem ≠ nil via Hitems_non_nil + Forall_lookup.
    - "found = false" leaf branches (height=0 or no children):
        NOT STARTED. Pure argument: children_sets = [] (or empty),
        so elems = list_to_set items, and find's postcondition gives
        ∀ j < idx, R items[j] key; ∀ j ≥ idx, R key items[j].
    - "found = false, children > 0" recursive branch:
        NOT STARTED. Requires:
        (1) Load child_locs[idx] via wp_load_slice_elem on Hchildren_own.
        (2) Extract idx-th child from big_sepL2 Hchildren_rep
            (big_sepL2_lookup_acc or similar).
        (3) Apply IH: wp_apply (IH true child_loc child_elems ...).
        (4) Reassemble node_repr_aux (put child back into big_sepL2).
        (5) Postcondition for result=nil uses btree_ordering + transitivity
            for children_sets[j≠idx], IH for children_sets[idx].
    - wp_auto FAILS between found=false and len(children) check
      (same exception_seq issue as items.v). Workaround: skip wp_auto,
      go straight to wp_if_destruct. *)

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
Proof. Admitted.

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
