# Candidate Lessons Learned — Session s4

## Proof-specific tactical knowledge (from ContainsRecursive)

### 1. Recursive functions require Löb induction before `wp_start`
For recursive Go functions, use `iLöb as "IH" forall (...).` BEFORE `wp_start`. The pattern is:
```coq
iLöb as "IH" forall (args...).
wp_start as "Hpre".
(* destruct precondition, case split, ... *)
wp_apply ("IH" $! args' with "[...]").
```
Using Coq-level `induction` + `iIntros` doesn't work because `wp_start` expects to introduce from a Hoare triple, and after manual `iIntros` the goal is already a WP. Using `wp_method_call`/`wp_call` as substitutes for `wp_start` is fragile (e.g., `wp_call` fails on method calls, `wp_auto` can't progress without the function being unfolded).

### 2. `wp_auto` eagerly resolves statically-known if-conditions
When a condition like `head == null` is known at proof time (e.g., `head` is literally `null` after `subst`), `wp_auto` will resolve the if and take the correct branch automatically — no `wp_if_destruct` needed. But when the condition is symbolic (e.g., `head` is an arbitrary `loc`), `wp_auto` stops before the if, and `wp_if_destruct` is needed to case-split.

### 3. `wp_auto` can handle both if-conditions in sequence
In `ContainsRecursive`, the first `wp_auto` in the inductive case handles allocation, loads, and stops at the first if (null check). After `wp_if_destruct` for the null check, the second `wp_if_destruct` for the value comparison works *immediately* — no `wp_auto` or `wp_pures` is needed between the two `wp_if_destruct` calls. Inserting `wp_auto` between them actually causes failures.

### 4. After recursive `wp_apply`: `wp_pures` for pure-only continuations, `wp_auto` when stores follow
- **Read-only recursive calls** (ContainsRecursive, CopyListRecursive): After `wp_apply ("IH" ...)` and `iIntros`, use `wp_pures` to process the `return:`/`exception_do` wrapping. `wp_auto` fails to progress here.
- **Mutating recursive calls** (InsertBackRecursive, DeleteAllRecursive): After `wp_apply ("IH" ...)` and `iIntros`, use `wp_auto` — it handles the store to `head.Next`, the load of `head` from the stack, and the return all at once. `wp_pures` alone can't handle the store (it's not a pure step), and `wp_store` fails because there are loads before the store that `wp_store` can't see past.

### 5. `wp_if_destruct` may substitute variables
In the true branch of `wp_if_destruct` on `hd_val == v`, `hd_val` gets substituted with `v` and disappears from the Coq context. Subsequent `iExists hd_val` will fail with "variable not found." Use the surviving name (`v`) instead.

### 6. Avoid the name `val` for existential witnesses
The name `val` conflicts with a Coq built-in (`language → Type`). Use `hd_val` or similar.

### 7. `is_list` vs `is_list_aux` in postconditions
The IH returns `is_list next S'` (with existential `n`), but reconstructing `is_list head ({[hd_val]} ∪ S')` requires a concrete witness for the outer `is_list_aux`. Extract the inner `n''` first with `iDestruct "Hlist" as (n'') "Hlist"`, then use `iExists (Datatypes.S n'')` for the outer.

### 8. `bool_decide` extensionality
To show `bool_decide (v ∈ {[hd_val]} ∪ S') = bool_decide (v ∈ S')` when `hd_val ≠ v`, use `f_equal. apply bool_decide_ext. set_solver.` — not `rewrite bool_decide_ext` (which fails due to type class inference).

## Additional lessons from InsertBackRecursive, DeleteAllRecursive, CopyListRecursive

### 9. Set difference reasoning: use `replace ... by set_solver`
For DeleteAllRecursive, the postcondition involves `S ∖ {[v]}`. The key set identities:
- `({[v]} ∪ S') ∖ {[v]} = S' ∖ {[v]}` (when hd_val = v)
- `({[hd_val]} ∪ S') ∖ {[v]} = {[hd_val]} ∪ (S' ∖ {[v]})` (when hd_val ≠ v)

These don't match `iEval (rewrite ...)` well because the rewrite lemmas (e.g., `union_comm_L`, `difference_union_distr_l_L`) need specific forms. Instead, use:
```coq
replace (({[v]} ∪ S') ∖ {[v]}) with (S' ∖ {[v]}) by set_solver.
```
This is more robust and readable.

### 10. Set commutativity for InsertBackRecursive
InsertBackRecursive's postcondition has `{[v]} ∪ S` but the inductive case constructs `{[hd_val]} ∪ ({[v]} ∪ S')`. The goal `{[v]} ∪ ({[hd_val]} ∪ S') = {[hd_val]} ∪ ({[v]} ∪ S')` is solved by `set_solver` in the `iPureIntro` step. No manual rewriting needed.

### 11. CopyListRecursive: `wp_pures` before `wp_alloc`
In CopyListRecursive's inductive case, after the recursive call returns, the next step is `GoAlloc` for the new node. But there are pure steps (composite literal construction) between the recursive result and the alloc. Use `wp_pures. wp_alloc newNode as "Hnew".` — without `wp_pures`, `wp_alloc` can't find the allocation.

### 12. CopyListRecursive: splitting resources for original vs copy
After proving the WP, use `iSplitL "Hval Hnext Hrest"` to give the original struct field points-to and original tail to the first conjunct (original list), and the new node + copy tail to the second conjunct (copy). The `iSplitL` naming is crucial for resource separation.

### 13. Mutating proofs consume `Hnext` via store
In InsertBackRecursive and DeleteAllRecursive, `wp_auto` after the recursive call handles the store `head.Next := result`. This implicitly consumes the old `Hnext : head.Next ↦ next` and produces `head.Next ↦ result`. After `wp_auto`, `Hnext` in the context now points to the new value, so when reconstructing `is_list_aux`, use the recursive call's result (e.g., `head''`) as the next pointer, not the original `next`.

### 14. Common proof skeleton for recursive linked list methods
All four recursive proofs follow this skeleton:
```coq
Proof.
  iLöb as "IH" forall (head S).
  wp_start as "Hlist".
  iDestruct "Hlist" as (n) "Hlist".
  destruct n as [|n'].
  - (* Base: head = null, S = ∅ *)
    iDestruct "Hlist" as "[%Hnull %Hempty]". subst.
    wp_auto. (* resolves null check, handles base case computation *)
    (* ... apply HΦ, construct postcondition ... *)
  - (* Inductive: n = S n' *)
    simpl.
    iDestruct "Hlist" as (hd_val next S') "(%Heq & Hval & Hnext & Hrest)". subst.
    wp_auto. (* handles up to first if *)
    wp_if_destruct.
    + (* head = null contradiction *)
      iExFalso.
      iApply (is_list_aux_non_null n' _).
      simpl. iExists hd_val, next, S'. iFrame. iPureIntro. done.
    + (* head ≠ null: main logic *)
      wp_pures. (* or nothing, depending on structure *)
      wp_apply ("IH" $! next S' with "[Hrest]").
      { iFrame "#". iExists n'. iFrame. }
      iIntros (...) "...".
      wp_auto. (* or wp_pures, depending on stores *)
      (* ... apply HΦ, reconstruct is_list ... *)
Qed.
```

## Framework gap

### `struct_field_ref` is abstract — no `l ≠ null` from struct-field pointsto
`struct_field_ref` is a typeclass method with no concrete definition visible in proofs. There is no lemma `p.[t, f] ↦ v -∗ ⌜p ≠ null⌝`. The workaround is to admit a helper like `is_list_aux_non_null`. This is the same gap identified in session s2. All four recursive proofs use this admitted helper for the `head = null` contradiction in the inductive case.
