From New.generatedproof Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.btree_proof Require Import btree_init rep.

(** * Specs for [items] slice helper methods.

    These are methods on [items] (a type alias for [[]Item]) used internally
    by the btree implementation. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx: GoContext}.

(** [items.find] performs binary search via [sort.Search].  It returns an
    index and a boolean indicating whether an R-equivalent item was found.

    - [found = true]: [items !! idx] is R-equivalent to [key]
    - [found = false]: [idx] is the insertion point; all items before [idx]
      satisfy [R item key], and all items from [idx] onward satisfy
      [R key item]. *)
Lemma wp_items__find (sl : slice.t) (items_list : list interface.t)
    (key : interface.t) R :
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
Admitted.

End proof.
