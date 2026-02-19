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

(** ** node.get *)

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
Proof.
Admitted.

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
Admitted.

End proof.
