# InsertFront Proof Log - 2026-03-10

## Plan

The goal is to prove `wp_ListNode__InsertFront` for a linked list with a gset-based representation invariant.

The Go function simply allocates a new ListNode with Val=v and Next=head, returning the pointer. The postcondition requires `is_list head' ({[v]} ∪ S)`.

### Strategy
1. Start with `wp_start as "Hlist".` then `wp_auto.` to handle straight-line code
2. After wp_auto, we should have a new struct allocated with Val=v and Next=head
3. Need to split the new struct into field pointstos (iStructNamed or similar)
4. Unfold `is_list` in goal, rewrite `size ({[v]} ∪ S)` to `S (size S)` using disjointness
5. Provide witnesses (v, head) and frame the field pointstos with the old `is_list head S`
6. Set arithmetic: `({[v]} ∪ S) ∖ {[v]} = S` when `v ∉ S`

### Key lemmas needed
- `size_union_alt` or `size_union`: `size ({[v]} ∪ S) = size {[v]} + size S` when disjoint
- `size_singleton`: `size {[v]} = 1`
- `set_solver` for membership/equality

## Attempt 1

- `wp_start` needs `intros Hnotin` first (pure Coq arrow before WP)
- After `wp_start as "Hlist". wp_auto.`, goal is:
  `WP exception_do (return: GoAlloc ListNode ...) {{ v, Φ v }}`
  wp_auto handled loads/lets but not the final allocation.
- `wp_alloc head' as "Hnew".` succeeded, giving:
  `"Hnew" : head' ↦ {| Val' := v; Next' := head |}`
  Goal: `WP exception_do (return: # head') {{ v, Φ v }}`
- Now need: handle exception_do/return (should be pure), split struct, apply postcondition.

## Attempt 2

- After `wp_alloc`, goal was `WP exception_do (return: #head') {{ v, Φ v }}`.
- `wp_auto` handled the exception_do/return reduction.
- `iStructNamed "Hnew"` split the struct pointsto into per-field pointstos.
- `iApply "HΦ"` applied the postcondition.
- Unfolded `is_list`, rewrote `size ({[v]} ∪ S)` using `size_union` + `size_singleton`.
- After `simpl`, `iExists v, head` provided witnesses.
- `iFrame` handled the field pointstos (Val and Next).
- `assert (({[v]} ∪ S) ∖ {[v]} = S) as Hdiff by set_solver` + `rewrite Hdiff` simplified the remaining set expression.
- Second `iFrame` handled `is_list_aux (size S) head S` from the "Hlist" hypothesis.
- `iPureIntro. set_solver.` closed the remaining pure goals (`v ∈ {[v]} ∪ S`).

## Result

Proof compiles with `Qed`. No admits remaining.

## Removing `v ∉ S` precondition

### Plan
1. Change `is_list_aux` to decouple `n` from `size S` -- use existential `S'` where `S = {[v]} ∪ S'` instead of `S ∖ {[v]}`
2. Change `is_list` to existentially quantify over `n`
3. Remove `v ∉ S` from InsertFront spec
4. Fix the proof -- should be simpler since we just need `{[v]} ∪ S = {[v]} ∪ S`

### Attempt 1 -- Success

Made all three changes in one pass:
1. Updated `is_list_aux` to use existential `S'` with `S = {[v]} ∪ S'` instead of `S ∖ {[v]}` and removed size constraint
2. Changed `is_list` to `∃ n, is_list_aux n p S`
3. Removed `v ∉ S` precondition and `intros Hnotin` from proof

New proof structure:
- `wp_start as "Hlist". wp_auto. wp_alloc head' as "Hnew". wp_auto.` -- same as before
- `iStructNamed "Hnew". iApply "HΦ".` -- same as before
- `unfold is_list. iDestruct "Hlist" as (n) "Hlist".` -- destruct the existential `n`
- `iExists (Datatypes.S n). simpl.` -- provide witness `n+1` for the new list
- `iExists v, head, S. iFrame.` -- witnesses: value is `v`, next is `head`, tail set is `S`
- `iPureIntro. set_solver.` -- proves `{[v]} ∪ S = {[v]} ∪ S`

Build succeeds, proof closes with `Qed`. No size arithmetic needed at all since `n` is decoupled from `size S`.
