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

(** ** Ordering interface

    [is_less_order R] asserts that the [Less] method on [interface.t] items
    correctly implements the abstract relation [R].  This is persistent and
    intended to be shared across all btree operations. *)

Definition is_less_order (R : interface.t → interface.t → Prop) : iProp Σ :=
  □ ∀ (x y : interface.t),
    ⌜x ≠ interface.nil⌝ -∗ ⌜y ≠ interface.nil⌝ -∗
    {{{ True }}}
      (interface.get #"Less"%go #x) #y
    {{{ (b : bool), RET #b; ⌜b ↔ R x y⌝ }}}.

(** ** Node representation invariant

    [node_repr_aux enforce_min height R n elems degree] asserts that [n : loc]
    points to a [btree.node] whose element set is [elems].

    When [enforce_min] is [true], minimum occupancy constraints are imposed
    (for interior/non-root nodes).  When [false], only the maximum is
    enforced (suitable for the root).

    The [height] parameter provides well-founded recursion.  At height [0]
    the node must be a leaf.  At height [S h] children are recursively
    represented at height [h].  Children always enforce minimum occupancy.
    Because the height is existentially quantified in practice, it acts as
    fuel rather than an exact measure. *)

Fixpoint node_repr_aux (enforce_min : bool) (height : nat)
    (R : interface.t → interface.t → Prop)
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

    (* ---- recursive: children (always enforce min) ---- *)
    "Hchildren_rep" ∷ (match height with
      | O   => ⌜child_locs = [] ∧ children_sets = []⌝
      | S h => [∗ list] cl;cs ∈ child_locs;children_sets,
                 node_repr_aux true h R cl cs degree
      end) ∗

    (* ---- pure: element set ---- *)
    "%Helems" ∷ ⌜elems = list_to_set items ∪ ⋃ children_sets⌝ ∗

    (* ---- pure: no nil items (needed to call Less via is_less_order) ---- *)
    "%Hitems_non_nil" ∷ ⌜Forall (λ x, x ≠ interface.nil) items⌝ ∗

    (* ---- pure: sorted ---- *)
    "%Hsorted" ∷ ⌜items_sorted R items⌝ ∗

    (* ---- pure: B-tree size invariants ----
       With [enforce_min]:
         Leaf:     len(items) ≤ degree - 1, no children.
         Internal: degree - 1 < len(items) < 2 * degree - 1,
                   len(children) = len(items) + 1.
       Without [enforce_min] (root):
         Either a leaf (no children) or internal
         (len(children) = len(items) + 1), with only the
         max-items bound. *)
    "%Hsize" ∷ ⌜if enforce_min then
                  ((length child_locs = 0 ∧
                    length items ≤ Z.to_nat (degree - 1)) ∨
                  (length child_locs = length items + 1 ∧
                   Z.to_nat (degree - 1) < length items ∧
                   length items < Z.to_nat (2 * degree - 1)))%nat
                else
                  ((length child_locs = 0 ∨
                    length child_locs = length items + 1) ∧
                   length items < Z.to_nat (2 * degree - 1))%nat⌝ ∗

    (* ---- pure: ordering ---- *)
    "%Hordering" ∷ ⌜btree_ordering R items children_sets⌝.

(** [node_repr] is the relaxed version without minimum occupancy,
    suitable for the root node and for specs of methods that do not
    depend on minimum occupancy (e.g. [get], [iterate]). *)
Definition node_repr := node_repr_aux false.

(** [node_repr_interior] enforces minimum occupancy, used for
    interior (non-root) nodes in the recursive structure. *)
Definition node_repr_interior := node_repr_aux true.

(** ** BTree representation invariant

    [btree_repr R t elems] asserts that [t : loc] points to a [btree.BTree]
    struct representing the set [elems], ordered by [R].

    Copy-on-write is ignored: the [cow] field is owned but unconstrained. *)

Definition btree_repr (R : interface.t → interface.t → Prop)
    (t : loc) (elems : gset interface.t) : iProp Σ :=
  ∃ (degree_val len_val : w64) (root_loc cow_loc : loc),
    (* ---- spatial: BTree struct fields ---- *)
    "Hdegree" ∷ t ↦s[btree.BTree :: "degree"] degree_val ∗
    "Hlength" ∷ t ↦s[btree.BTree :: "length"] len_val ∗
    "Hroot_field" ∷ t ↦s[btree.BTree :: "root"] root_loc ∗
    "Hcow_field" ∷ t ↦s[btree.BTree :: "cow"] cow_loc ∗

    (* ---- pure: degree validity ---- *)
    "%Hdegree_pos" ∷ ⌜(1 < uint.Z degree_val)%Z⌝ ∗

    (* ---- pure: length tracks set cardinality ---- *)
    "%Hlen" ∷ ⌜uint.Z len_val = Z.of_nat (size elems)⌝ ∗

    (* ---- root: null means empty, otherwise node_repr (relaxed) ---- *)
    "Hroot" ∷ (if decide (root_loc = null) then
                 ⌜elems = ∅⌝
               else
                 ∃ height, node_repr height R root_loc elems (uint.Z degree_val)).

End proof.
