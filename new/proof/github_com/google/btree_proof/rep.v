From New.generatedproof.github_com.google Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof.github_com.google.btree_proof Require Import btree_init.

(** * Representation invariant for btree.node

    B-trees are of order [2 * degree - 1], where [degree] is user-specified.
    [node_repr] relates a heap-allocated [btree.node] to a [gset] of all items
    reachable from that subtree.
*)

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : btree.Assumptions}.
Collection W := sem + package_sem.

(** ** Pure definitions *)

(** Sorted: every pair of elements at indices [i < j] satisfies [R]. *)
Definition items_sorted (R : interface.t → interface.t → Prop)
    (items : list interface.t) : Prop :=
  ∀ (i j : nat), (i < j)%nat →
    ∀ xi xj, items !! i = Some xi → items !! j = Some xj → R xi xj.

(** B-tree ordering invariant between items and children element sets.

    For a node with [n] items and [n+1] children [c₀, …, cₙ]:
    - Upper bound: for child [i < n], all elements in [cᵢ] satisfy
        [R e items[i]].
    - Lower bound: for child [i > 0], all elements in [cᵢ] satisfy
        [R items[i-1] e].

    Together these give the standard interleaving:
      c₀ < x₀ < c₁ < x₁ < … < x_{n-1} < cₙ *)
Definition btree_ordering (R : interface.t → interface.t → Prop)
    (items : list interface.t)
    (children_sets : list (gset interface.t)) : Prop :=
  (* upper bound: child i < items[i] *)
  (∀ (i : nat) (s : gset interface.t) (x : interface.t),
    children_sets !! i = Some s →
    items !! i = Some x →
    ∀ e, e ∈ s → R e x) ∧
  (* lower bound: items[i-1] < child i *)
  (∀ (i : nat) (s : gset interface.t) (x : interface.t),
    (0 < i)%nat →
    children_sets !! i = Some s →
    items !! (i - 1)%nat = Some x →
    ∀ e, e ∈ s → R x e).

(** ** Less function spec

    [is_less_fn R] asserts that the [Less] method correctly
    implements the abstract relation [R].  This is persistent and
    intended to be shared across all btree operations. *)

(** [is_less_fn R] asserts that the [Less] interface method on any
    non-nil [Item] correctly implements the abstract relation [R].
    This is persistent. *)
Definition is_less_fn (R : interface.t → interface.t → Prop) : iProp Σ :=
  □ ∀ (i : interface.t_ok) (y : interface.t),
    {{{ True }}}
      #(methods i.(interface.ty) "Less"%go i.(interface.v)) #y
    {{{ (b : bool), RET #b; ⌜b ↔ R (interface.ok i) y⌝ }}}.

(** ** Node representation invariant

    [node_repr_aux enforce_min height R n elems degree] asserts that
    [n : loc] points to a [btree.node] whose element set is [elems].

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
  ∃ (items_sl children_sl : slice.t) (cow_val : loc)
    (items_list : list interface.t)
    (child_locs : list loc)
    (children_sets : list (gset interface.t)),

    (* ---- spatial: per-field struct ownership ---- *)
    "Hitems" ∷ n.[btree.node.t, "items"] ↦ items_sl ∗
    "Hchildren" ∷ n.[btree.node.t, "children"] ↦ children_sl ∗
    "Hcow" ∷ n.[btree.node.t, "cow"] ↦ cow_val ∗

    (* ---- spatial: slice contents ---- *)
    "Hitems_own" ∷ items_sl ↦* items_list ∗
    "Hchildren_own" ∷ children_sl ↦* child_locs ∗

    (* ---- recursive: children (always enforce min) ---- *)
    "Hchildren_rep" ∷ (match height with
      | O   => ⌜child_locs = [] ∧ children_sets = []⌝
      | S h => [∗ list] cl;cs ∈ child_locs;children_sets,
                 node_repr_aux true h R cl cs degree
      end) ∗

    (* ---- pure: element set ---- *)
    "%Helems" ∷ ⌜elems = list_to_set items_list ∪ ⋃ children_sets⌝ ∗

    (* ---- pure: no nil items (needed to call Less via is_less_fn) ---- *)
    "%Hitems_non_nil" ∷ ⌜Forall (λ x, x ≠ interface.nil) items_list⌝ ∗

    (* ---- pure: sorted ---- *)
    "%Hsorted" ∷ ⌜items_sorted R items_list⌝ ∗

    (* ---- pure: B-tree size invariants ---- *)
    "%Hsize" ∷ ⌜if enforce_min then
                  ((length child_locs = 0 ∧
                    length items_list ≤ Z.to_nat (degree - 1)) ∨
                  (length child_locs = length items_list + 1 ∧
                   Z.to_nat (degree - 1) < length items_list ∧
                   length items_list < Z.to_nat (2 * degree - 1)))%nat
                else
                  ((length child_locs = 0 ∨
                    length child_locs = length items_list + 1) ∧
                   length items_list < Z.to_nat (2 * degree - 1))%nat⌝ ∗

    (* ---- pure: ordering ---- *)
    "%Hordering" ∷ ⌜btree_ordering R items_list children_sets⌝.

(** [node_repr] is the relaxed version without minimum occupancy,
    suitable for the root node and for specs of methods that do not
    depend on minimum occupancy (e.g. [get], [iterate]). *)
Definition node_repr := node_repr_aux false.

(** [node_repr_interior] enforces minimum occupancy, used for
    interior (non-root) nodes in the recursive structure. *)
Definition node_repr_interior := node_repr_aux true.

(** ** BTree representation invariant

    [btree_repr R t elems] asserts that [t : loc] points to a
    [btree.BTree] struct representing the set [elems], ordered by [R].

    Copy-on-write is ignored: the [cow] field is owned but unconstrained. *)

Definition btree_repr (R : interface.t → interface.t → Prop)
    (t : loc) (elems : gset interface.t) : iProp Σ :=
  ∃ (degree_val length_val : w64) (root_val cow_val : loc),
    (* ---- spatial: per-field BTree struct ownership ---- *)
    "Hdegree" ∷ t.[btree.BTree.t, "degree"] ↦ degree_val ∗
    "Hlength" ∷ t.[btree.BTree.t, "length"] ↦ length_val ∗
    "Hroot_pt" ∷ t.[btree.BTree.t, "root"] ↦ root_val ∗
    "Hcow" ∷ t.[btree.BTree.t, "cow"] ↦ cow_val ∗

    (* ---- pure: degree validity ---- *)
    "%Hdegree_pos" ∷ ⌜(1 < uint.Z degree_val)%Z⌝ ∗

    (* ---- pure: length tracks set cardinality ---- *)
    "%Hlen" ∷ ⌜uint.Z length_val = Z.of_nat (size elems)⌝ ∗

    (* ---- root: null means empty, otherwise node_repr (relaxed) ---- *)
    "Hroot" ∷ (if decide (root_val = null) then
                 ⌜elems = ∅⌝
               else
                 ∃ height, node_repr height R root_val
                                     elems (uint.Z degree_val)).

End proof.
