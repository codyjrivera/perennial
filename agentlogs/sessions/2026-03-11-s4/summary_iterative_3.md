# Session Summary: `ece52d17` — InsertBack Qed, CopyList Qed, DeleteAll in progress

## Session Stats

| Stat | Value |
|------|-------|
| Session ID | `ece52d17-d0e8-44c5-ba9c-2e5c5ec9112a` (continued) |
| Session dir | `agentlogs/sessions/2026-03-18-s1/` |
| Model | `claude-opus-4-6` (proof work); `claude-sonnet-4-6` (summarization) |
| Window | 2026-03-19T04:58–05:46 UTC (~48 min of proof work) |
| Output tokens | ~80K |
| Cache reads | ~12.8M |
| Cache creates | ~762K |

*Note: 04:36–04:58 UTC was summarization work (writing `summary_iterative_2.md`).
Proof work began at 04:58 UTC. This summary covers only proof work, not the summarization phase.*

---

## Research (~8 min, 05:07–05:11 + 05:30–05:32 UTC)

- Spawned Explore sub-agent to find CopyList and DeleteAll Go implementations and check
  for existing recursive proofs in the proof file. Retrieved full GooseLang translations
  for both methods.
- Read `wp_for` reference section (lines 283–361) before starting DeleteAll, to understand
  compound condition handling, loop body/exit splitting, and `wp_end` usage.

---

## Planning

- **InsertBack**: No new planning; continued from compacted context. Issues were all in the
  compile-and-fix loop.
- **CopyList**: Designed loop invariant tracking two simultaneous structures — original list
  segment + remaining, and new list segment + tail node with fields exposed. Key insight:
  the tail node's fields must be in the invariant so the body can store into `tail.Next`.
  Also identified: CopyList's `head_ptr` doesn't persist to the loop (confirmed by probing).
- **DeleteAll**: Designed loop 1 invariant (`is_list head_loc S_rem` + purity about `S ∖ {[v]}`).
  Identified that compound conditions (`head != nil && head.Val == v`) require the list to
  be destructed inside the loop body before `wp_auto` can evaluate the full condition.
  Identified that the exit branch from `wp_for` for loop 1 contains the entire second loop
  as continuation code.

---

## Implementing

### InsertBack (~10 min, 04:58–05:07 UTC → Qed)

Continued from the `assert` fix that had been written but not compiled.

4 compile iterations:

1. **`assert` parses correctly but `S` is `nat → nat`** (04:58): The `assert`
   avoids the ssreflect parsing issue, but `S` has been substituted away by `%Heq`.
   Fix: write `{[hd_val]} ∪ S'` instead of `S` in the assert and in the `iApply`
   argument to `is_list_seg_to_list`.

2. **`done` fails for `{[v]} = {[v]} ∪ ∅`** (05:00): After `iPureIntro`, the remaining
   goal contains a set equality that `done` can't prove syntactically. Fix: `set_solver`.

3. **`wp_auto` fails in loop body** (05:01): Same "Failed to progress" as in the prior
   session. Fix confirmed: use `wp_pures` instead (body is processed by `wp_for`'s
   internal machinery; `wp_pures` handles the remaining pure steps).

4. **`rewrite Heq2. rewrite HS.` fails** (05:04–05:06): `%Heq2` auto-substituted `S_rest`,
   so `Heq2` is gone from the context. Fix: remove both rewrites and use `set_solver`
   directly, which finds the relevant equalities (`HS`, `Hempty`, `Heq2`) in context.

**InsertBack: Qed at 05:07 UTC.**

---

### CopyList (~22 min, 05:07–05:29 UTC → Qed)

CopyList iteratively copies a list using a `tail` pointer:
```go
func (head *ListNode) CopyList() *ListNode {
    if head == nil { return nil }
    newHead := &ListNode{Val: head.Val}
    cur := head.Next; tail := newHead
    for cur != nil {
        tail.Next = &ListNode{Val: cur.Val}
        tail = tail.Next; cur = cur.Next
    }
    return newHead
}
```

Loop invariant (two list structures tracked simultaneously):
```
∃ cur_loc tail_loc tail_val n_orig n_new S_orig_prefix S_new_prefix S_rest,
  "cur"     ∷ cur_ptr ↦ cur_loc ∗
  "tail"    ∷ tail_ptr ↦ tail_loc ∗
  "newHead" ∷ newHead_ptr ↦ newHead_loc ∗
  "Htv"     ∷ tail_loc.[Val] ↦ tail_val ∗
  "Htn"     ∷ tail_loc.[Next] ↦ null ∗
  "Horig"   ∷ is_list_seg n_orig head S_orig_prefix cur_loc ∗
  "Hrest"   ∷ is_list cur_loc S_rest ∗
  "Hnew"    ∷ is_list_seg n_new newHead_loc S_new_prefix tail_loc ∗
  ⌜S = S_orig_prefix ∪ S_rest⌝ ∗
  ⌜S_orig_prefix = S_new_prefix ∪ {[tail_val]}⌝
```

7 compile iterations:

**1. `head_ptr` not found** (~4 min, 05:11–05:22): The invariant included `"head" ∷ head_ptr ↦ head`. Multiple probing attempts (`iExact "head"`, `"head0"`, `"$head"`, `iNamedAccu`, `iPureIntro`) confirmed:
- `"head"` hypothesis does not exist in scope after `wp_auto`
- The WP term uses `cur_ptr`, `tail_ptr`, `newHead_ptr` — no `head_ptr`
- `head_ptr` was consumed or not created; CopyList's return is `newHead_ptr`, so `head_ptr` is not needed after the preamble
- Fix: remove `head_ptr` from the invariant and resource list.

**2. `S` is `nat → nat` in exit branch** (~2 min, 05:22–05:24): Same substitution as InsertBack. `%Heq` substituted `S → {[hd_val]} ∪ S'`. Any reference to `S` in `assert` or `iApply` fails. Fix: use substituted forms explicitly. Also: `%HSnew` substituted `S_orig_prefix → S_new_prefix ∪ {[tail_val]}`, so that variable is also gone. Use `set_solver` to prove the set equality needed.

**3. `wp_for_post: not a for_postcondition`** (~2 min, 05:24–05:26): In the loop body, after `wp_alloc + iStructNamed`, used `wp_pures` but then `wp_for_post` failed. The body has stores (`tail.Next = new_node`, `tail = tail.Next`, `cur = cur.Next`) which `wp_pures` can't handle. Fix: use `wp_auto` instead of `wp_pures` after `iStructNamed`.

**4. `S_orig_prefix` not found in body branch** (~2 min, 05:26–05:28): After `wp_auto` + `wp_for_post`, the `iExists` referenced `S_orig_prefix ∪ {[cur_val]}`. But `%HSnew` substituted `S_orig_prefix` away in the body branch too. Fix: replace `S_orig_prefix` with `S_new_prefix ∪ {[tail_val]}` in all body branch `iExists` witnesses.

**CopyList: Qed at 05:29 UTC.**

---

### DeleteAll (in progress, ~16 min, 05:30–05:46 UTC)

DeleteAll has two loops:
- **Loop 1**: Remove matching nodes from the front (`for head != nil && head.Val == v`)
- **Loop 2**: Remove matching nodes from middle/back (`for cur != nil && cur.Next != nil`)

The compound conditions (`&&`) require the list to be destructed INSIDE the loop body
before `wp_auto` can load the Val field.

5 compile iterations:

**1. `iExistDestruct` fails** (05:37): Original invariant used `is_list_aux n_hd` as an
existential inside the `iAssert`, AND separately introduced `n_hd` via `iDestruct "Hlist" as (n_hd)` before the `iAssert`. After `wp_for "IH1"`, the invariant's `n_hd` was renamed to `n_hd0` to avoid collision, so `destruct n_hd` (which targeted the outer variable) didn't affect `is_list_aux n_hd0`. Then `iDestruct "Hlist" as "[%Hnull %Hempty]"` tried to destruct `is_list_aux n_hd0` (still existential, not simplified) and failed.
Fix: use `is_list` (not `is_list_aux n`) in the invariant; destruct to `is_list_aux n_hd` inside the loop body after `wp_for "IH1"`.

**2. `wp_if_destruct` fails on nested decides** (05:41): After `wp_auto` evaluates the loop 1 condition with `head = null`, the condition is `#false`. The goal becomes:
```
if decide (#false = #true) then WP (loop body) {{ ... }}
else if decide (#false = #false) then WP (continuation with loop 2 + return) {{ Φ }}
else False
```
`wp_if_destruct` expects a GooseLang-level `if: #b then ... else ...` but gets a Coq-level nested `if decide`. It fails with "No matching clauses".

**3. Condition still unresolved after `wp_auto`** (05:43): `wp_auto` was called again hoping to simplify the decides, but the goal remained `if decide (#false = #true) then ...`. The `iPureIntro` probe showed the full goal — `wp_auto` does not simplify Coq-level `if decide`.

**Session interrupted here.** The pending fix is to resolve the `if decide` structure using `rewrite decide_False; [|discriminate]. rewrite decide_True; [|reflexivity].` — this was the next edit prepared but not yet compiled.

**Key discovery about DeleteAll's exit branch**: The goal in the exit branch is not `Φ (head)` (as it was in InsertBack), but rather `WP (exception_do (execute_val ;;; let "cur" := ... for: loop2 ... return: head) {{ Φ }})`. After loop 1 exits, the entire second loop is still in the continuation and must be proven.

---

## Progress Summary

| Proof | Status |
|---|---|
| `wp_ListNode__Contains` | Qed (prior session) |
| `wp_ListNode__InsertBack` | **Qed** (this session) |
| `wp_ListNode__CopyList` | **Qed** (this session) |
| `wp_ListNode__DeleteAll` | In progress — loop 1 structure understood, stuck on `if decide` resolution |

---

## Recurring Patterns Discovered

**Variable substitution by `%` patterns** (seen in InsertBack, CopyList, DeleteAll):
When Iris `%Heq` introduces a pure fact of the form `X = expr`, Coq substitutes the variable `X` away. This causes any later reference to `X` by name (in `assert`, `iExists`, `iApply` arguments) to fail with "nat → nat" or "not found". Fix: always use the substituted form (e.g., `{[hd_val]} ∪ S'` instead of `S`), or use `set_solver` which finds equalities automatically.

**`wp_auto` vs `wp_pures` in loop bodies after `wp_alloc`**:
- If body is pure (no loads/stores after alloc): `wp_pures` works, then `wp_for_post`
- If body has loads/stores after alloc: `wp_auto` required (not `wp_pures`)
- If body is all pure (no alloc at all): `wp_for` handles internally, body goal is already `for_postcondition`

---

## What Remains

1. **DeleteAll: resolve `if decide (#false = #true)` after loop 1 exits (null case).**
   Try `rewrite decide_False; [|discriminate]. rewrite decide_True; [|reflexivity].`
   If that works, the null case exit leads to `WP (loop 2 continuation)`. Since head was
   null, cur = null, loop 2 condition is immediately false, and return is null.

2. **DeleteAll: non-null loop 1 body and exit branches.** After `wp_auto` with
   head ≠ null and head.Val = v (or ≠ v), need to handle the body (`wp_for_post` +
   invariant update) and exit (proceed to loop 2 with `head.Val ≠ v` invariant).

3. **DeleteAll: loop 2.** Compound condition `cur != nil && cur.Next != nil`, body with
   an if-else (unlink or advance). The inner `if` inside the loop body will require another
   `wp_if_destruct`. `cur.Next.Val` requires destructing `is_list cur.Next ...`.
