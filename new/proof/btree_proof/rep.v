From New.generatedproof Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.btree_proof Require Import btree_init.

(** * Representation invariant for btree.node

    B-trees are of order [2 * degree - 1], where [degree] is user-specified.
    [node_repr] relates a heap-allocated [btree.node] to a [gset] of all items
    reachable from that subtree.
*)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx: GoContext}.

(** ** Pure definitions *)

(** Sorted: every pair of elements at indices [i < j] satisfies [R]. *)
Definition items_sorted (R : interface.t → interface.t → Prop)
    (items : list interface.t) : Prop :=
  ∀ (i j : nat), (i < j)%nat →
    ∀ xi xj, items !! i = Some xi → items !! j = Some xj → R xi xj.

(** B-tree ordering invariant between items and children element sets.

    For a node with [n] items and [n+1] children:
    - For each child [i] with [i < n]:
        all elements in [children_sets !! i] are [R]-less than [items !! i]
    - For the last child [n]:
        all elements are [R]-greater than [items !! (n - 1)]

    NOTE: this follows the pseudo-code specification.  It gives upper bounds
    for children [0 .. n-1] and a lower bound only for the last child.
    For the full interleaving property, intermediate children also need
    lower bounds (i.e., [R (items !! (i-1)) e] for [0 < i]). *)
Definition btree_ordering (R : interface.t → interface.t → Prop)
    (items : list interface.t)
    (children_sets : list (gset interface.t)) : Prop :=
  (* upper bound: for each child i < len(children) - 1, elements < items[i] *)
  (∀ (i : nat) (s : gset interface.t) (x : interface.t),
    (i < length children_sets - 1)%nat →
    children_sets !! i = Some s →
    items !! i = Some x →
    ∀ e, e ∈ s → R e x) ∧
  (* lower bound: for the last child, elements > last item *)
  (∀ (s : gset interface.t) (x : interface.t),
    children_sets !! (length children_sets - 1)%nat = Some s →
    items !! (length items - 1)%nat = Some x →
    ∀ e, e ∈ s → R x e).

(** ** Node representation invariant

    [node_repr height R n elems degree] asserts that [n : loc] points to a
    [btree.node] whose element set is [elems].

    The [height] parameter provides well-founded recursion.  At height [0]
    the node must be a leaf.  At height [S h] children are recursively
    represented at height [h].  Because the height is existentially
    quantified in practice, it acts as fuel rather than an exact measure. *)

Fixpoint node_repr (height : nat) (R : interface.t → interface.t → Prop)
    (n : loc) (elems : gset interface.t) (degree : Z)
    {struct height} : iProp Σ :=
  ∃ (items_sl children_sl : slice.t)
    (items : list interface.t)
    (child_locs : list loc)
    (children_sets : list (gset interface.t)),

    (* ---- spatial: struct field ownership ---- *)
    "Hitems_field" ∷ n ↦s[btree.node :: "items"] items_sl ∗
    "Hchildren_field" ∷ n ↦s[btree.node :: "children"] children_sl ∗

    (* ---- spatial: slice contents ---- *)
    "Hitems_own" ∷ items_sl ↦* items ∗
    "Hchildren_own" ∷ children_sl ↦* child_locs ∗

    (* ---- recursive: children ---- *)
    "Hchildren_rep" ∷ (match height with
      | O   => ⌜child_locs = [] ∧ children_sets = []⌝
      | S h => [∗ list] cl;cs ∈ child_locs;children_sets,
                 node_repr h R cl cs degree
      end) ∗

    (* ---- pure: element set ---- *)
    "%Helems" ∷ ⌜elems = list_to_set items ∪ ⋃ children_sets⌝ ∗

    (* ---- pure: sorted ---- *)
    "%Hsorted" ∷ ⌜items_sorted R items⌝ ∗

    (* ---- pure: B-tree size invariants ----
       Leaf:     len(items) ≤ degree - 1, no children.
       Internal: degree - 1 < len(items) < 2 * degree - 1,
                 len(children) = len(items) + 1. *)
    "%Hsize" ∷ ⌜((length child_locs = 0 ∧
                  length items ≤ Z.to_nat (degree - 1)) ∨
                (length child_locs = length items + 1 ∧
                 Z.to_nat (degree - 1) < length items ∧
                 length items < Z.to_nat (2 * degree - 1)))%nat⌝ ∗

    (* ---- pure: ordering ---- *)
    "%Hordering" ∷ ⌜btree_ordering R items children_sets⌝.

End proof.
