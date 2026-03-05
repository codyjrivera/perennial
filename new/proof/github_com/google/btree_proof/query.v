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
    #t @! (go.PointerType (btree.BTree)) @! "Len" #()
  {{{ (n : w64), RET #n;
      btree_repr R t elems ∗
      ⌜uint.Z n = Z.of_nat (size elems)⌝ }}}.
Proof. Admitted.

(** ** node.get *)

Lemma wp_node__get enforce_min height R
    `{!RelDecision R, !Transitive R}
    (n : loc) (elems : gset interface.t)
    (degree : Z) (key : interface.t) :
  {{{ is_pkg_init btree ∗
      node_repr_aux enforce_min height R n elems degree ∗
      is_less_fn R }}}
    #n @! (go.PointerType (btree.node)) @! "get" #key
  {{{ (result : interface.t) (found : bool), RET (#result, #found);
      node_repr_aux enforce_min height R n elems degree ∗
      ⌜if found then
         result ∈ elems ∧ ¬R result key ∧ ¬R key result
       else
         ∀ e, e ∈ elems → R e key ∨ R key e⌝ }}}.
Proof. Admitted.

(** ** BTree.Get *)

Lemma wp_BTree__Get R `{!RelDecision R, !Transitive R}
    (t : loc) (elems : gset interface.t)
    (key : interface.t) :
  {{{ is_pkg_init btree ∗
      btree_repr R t elems ∗
      is_less_fn R }}}
    #t @! (go.PointerType (btree.BTree)) @! "Get" #key
  {{{ (result : interface.t) (found : bool), RET (#result, #found);
      btree_repr R t elems ∗
      ⌜if found then
         result ∈ elems ∧ ¬R result key ∧ ¬R key result
       else
         ∀ e, e ∈ elems → R e key ∨ R key e⌝ }}}.
Proof. Admitted.

(** ** BTree.Has *)

Lemma wp_BTree__Has R `{!RelDecision R, !Transitive R}
    (t : loc) (elems : gset interface.t)
    (key : interface.t) :
  {{{ is_pkg_init btree ∗
      btree_repr R t elems ∗
      is_less_fn R }}}
    #t @! (go.PointerType (btree.BTree)) @! "Has" #key
  {{{ (b : bool), RET #b;
      btree_repr R t elems ∗
      ⌜b ↔ ∃ e, e ∈ elems ∧ ¬R e key ∧ ¬R key e⌝ }}}.
Proof. Admitted.

End proof.
