# Session Summary: `ece52d17` — Iterative Unsorted List Proofs

## Session Stats

| Stat | Value |
|------|-------|
| Session ID | `ece52d17-d0e8-44c5-ba9c-2e5c5ec9112a` |
| Model | `claude-opus-4-6` |
| Window 1 | 2026-03-12T03:47–04:05 UTC (~18 min; hit daily limit) |
| Window 2 | 2026-03-12T15:57–16:48 UTC (~51 min; hit daily limit) |
| Total iterative wall time | ~69 min |
| Output tokens (iterative) | ~132K |
| Cache reads (iterative) | ~19M |
| Cache creates (iterative) | ~743K |

*Note: This session also proved 4 recursive methods earlier (~75 min, ~100K output tokens,
summarized in `summary.md`). The agentlogs s4 summary written by the agent at session end
covered only the recursive portion.*

*Note on other 3/11–3/12 sessions: `831d2cbd` (s3) was an administrative session that
summarized s2's ContainsRecursive work. `7660692b` (Mar 12 12:04, not in agentlogs) was a
memory-backup session. Neither contained proof work.*

---

## Research (~30 min, across both windows)

- Read all four iterative Go implementations from the generated code.
- Spawned 3 Explore sub-agents to find `wp_for` patterns; identified `insertionSort.v` and
  `search.v` as canonical examples, learning the `iAssert` + `wp_for "HI"` + `wp_if_destruct`
  + `wp_for_post` pattern.
- After the first limit reset, a sub-agent focused on early returns inside loops
  (`exception_do` / `wp_for_post_return`) found the relevant `PureWp` instances, but this
  knowledge was not actionable before the second limit hit.

---

## Planning (~10 min)

Proposed `is_list_seg` as the loop invariant backbone:

```coq
Fixpoint is_list_seg (n : nat) (from : loc) (S : gset w64) (to : loc) : iProp Σ :=
  match n with
  | 0 => ⌜from = to⌝ ∗ ⌜S = ∅⌝
  | S n' => ∃ hd_val next S', ⌜S = {[hd_val]} ∪ S'⌝ ∗
              from.["Val"] ↦ hd_val ∗ from.["Next"] ↦ next ∗
              is_list_seg n' next S' to
  end
```

Helper lemmas planned: `is_list_seg_append` (admitted), `is_list_seg_snoc` (proved),
`is_list_seg_to_list` (proved).

For Contains, the loop invariant partitions the list:
- `is_list_seg n_prefix head S_prefix cur` — already-traversed prefix
- `is_list cur S_rest` — remaining tail from current node
- `S = S_prefix ∪ S_rest` — partition condition
- `v ∉ S_prefix` — v not found so far

---

## Implementing

### Infrastructure (~8 min, 03:50–03:58 UTC)

Added `is_list_seg` and helpers. One Edit failed because three stub lemmas shared identical
`Proof. Admitted.` strings (`replace_all=false`); fixed by providing more surrounding context.
Infrastructure compiled cleanly.

### Contains (~38 min; `Qed` at 16:16 UTC)

Used `wp_for "IH"` with the planned invariant via `iAssert`. See stuck points 2–5.

### InsertBack (~32 min; incomplete at limit)

Never resolved the correct tactic sequence for the non-null branch. See stuck points 6–7.

### DeleteAll, CopyList

Not started.

---

## Stuck Points (Chronological)

**1. Edit string collision** (~2 min, 03:50 UTC)
Three stubs shared identical `Proof. Admitted.` text → `replace_all=false` error.
Fixed by using extended context in the Edit call.

**2. Contains: wrong `iExists` order in invariant init** (~3 min, 16:01–16:03 UTC)
`iExists head, 0%nat, ∅, S` was wrong; `$cur` already bound the pointer. Fixed by removing
`head`.

**3. Contains: null contradiction in loop body** (~2 min, 16:03–16:05 UTC)
`subst; done` failed to close the impossible `n_rest = 0` case. Required the admitted
`is_list_aux_non_null` helper (same gap as recursive proofs; `struct_field_ref` is abstract).

**4. Contains: `wp_if_destruct` branches reversed** (~5 min, 16:05–16:10 UTC)
Branch 1 = loop exit (cur = null, returns false); branch 2 = loop body (cur ≠ null) — opposite
of what the agent assumed. Required deliberate failing probe tactics to determine which was which.

**5. Contains: resource extraction order** (~3 min, 16:11–16:13 UTC)
Tried `iApply is_list_seg_to_list` after giving away `Hrest`, but `S_rest` was still needed to
close the false branch. Fixed by extracting `is_list null` before `iFrame`.

**6. InsertBack: `wp_auto` stops at `GoAlloc`, not at `if`** (~10 min, 16:16–16:35 UTC)
InsertBack allocates a new node *before* the null check. `wp_auto` stopped at `GoAlloc
ListNode` rather than proceeding to the `if head == null` check. Required explicit
`wp_alloc newNode_loc as "Hnew"` + `iStructNamed "Hnew"` + a second `wp_auto`.
After this, `wp_if_destruct` still failed ("No matching clauses for match"), indicating
the goal was not at an `if`.

**7. InsertBack: goal is `WP exception_do (for ...)`, not `WP if`** (~20 min, 16:35–16:48 UTC)
Probing revealed the goal after the preamble was `WP exception_do ((for: ...) ...)` — the
outer `exception_do` of the function body had not been unwrapped, and the goal was already
inside the loop body, not at the null-check `if`. Tried `wp_load`, `wp_store`, `wp_pures`,
`wp_for`, `wp_alloc`, `iPureIntro` — all failed. The third Explore sub-agent (16:32–16:33)
confirmed `wp_for_post_return` exists for early returns, but the agent could not apply this
knowledge to the actual goal shape. Session hit the daily limit with this stuck point
unresolved.

---

## Progress Summary

| Proof | Status |
|---|---|
| `wp_ListNode__Contains` | **Qed** |
| `wp_ListNode__InsertBack` | Incomplete — stuck at non-null branch |
| `wp_ListNode__DeleteAll` | Not started |
| `wp_ListNode__CopyList` | Not started |

**Infrastructure**: `is_list_seg`, `is_list_seg_snoc`, `is_list_seg_to_list` proved;
`is_list_seg_append` admitted.

---

## What Remains

1. **InsertBack: resolve `WP exception_do (for ...)` in the non-null branch.** The root issue
   is that InsertBack's structure differs from `insertionSort.v`/`search.v`: it allocates a new
   node before the loop, with an early return in the null branch. This means the goal after
   `wp_alloc` + `iStructNamed` + `wp_auto` is already inside the outer `exception_do`, at
   `WP for ...`, not at a plain `if`. The correct approach is likely to probe the goal
   state step-by-step (e.g., print goal after each tactic) before applying `wp_if_destruct`,
   and to use `wp_for` directly once at the right goal rather than relying on `wp_auto` to
   navigate past the preamble.

2. **DeleteAll and CopyList** — not attempted; should follow once InsertBack is understood.

3. **Fill `is_list_aux_non_null`** (ongoing gap from recursive proofs).
