From New.generatedproof Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.btree_proof Require Import btree_init rep.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx: GoContext}.

(** [node.get] finds the given key in the subtree and returns it, or
    [interface.nil] if not present.

    TODO: strengthen postcondition to identify *which* item is returned
    (the unique [x ∈ elems] with [¬R x key ∧ ¬R key x]). *)

Lemma wp_node__get (height : nat) (R : interface.t → interface.t → Prop)
    (n_loc : loc) (key : interface.t) (elems : gset interface.t) (degree : Z) :
  {{{ is_pkg_init btree ∗ node_repr height R n_loc elems degree }}}
    n_loc @ (ptrT.id btree.node.id) @ "get" #key
  {{{ (result : interface.t), RET #result;
      node_repr height R n_loc elems degree ∗
      ⌜(result ≠ interface.nil → result ∈ elems) ∧
       (result = interface.nil → key ∉ elems)⌝ }}}.
Proof.
Admitted.

End proof.
