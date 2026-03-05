From New.generatedproof.github_com.google Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.github_com.google.btree_proof Require Import btree_init rep.
From New.proof.sort_proof Require Import search.

(** * Specs for [items] slice helper methods. *)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : btree.Assumptions}.
Collection W := sem + package_sem.

Set Default Proof Using "All".

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

(** [items.find] now obtains the ordering from the [Item.Less] interface
    method rather than a separate [less_fn] parameter. *)
Lemma wp_items__find (sl : slice.t) (items_list : list interface.t)
    (key : interface.t)
    (R : interface.t → interface.t → Prop)
    `{!RelDecision R, !Transitive R} :
  {{{ is_pkg_init btree ∗
      sl ↦* items_list ∗
      is_less_fn R ∗
      ⌜items_sorted R items_list⌝ }}}
    sl @! (btree.items) @! "find" #key
  {{{ (idx : w64) (found : bool), RET (#idx, #found);
      sl ↦* items_list ∗
      ⌜if found then
         ∃ e, items_list !! uint.nat idx = Some e ∧ ¬R e key ∧ ¬R key e
       else
         (uint.nat idx ≤ length items_list)%nat ∧
         (∀ j e, items_list !! j = Some e → (j < uint.nat idx)%nat → R e key) ∧
         (∀ j e, items_list !! j = Some e → (uint.nat idx ≤ j)%nat → R key e)⌝ }}}.
Proof. Admitted.

End proof.
