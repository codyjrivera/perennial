# Session 2026-03-18-s1: Iterative linked-list proofs

## Goal
Prove iterative versions of Contains, InsertBack, CopyList, DeleteAll.
Contains was proved in the previous context. This session continues with InsertBack.

## Key discoveries so far

### wp_auto stops at struct alloc
For InsertBack, `wp_auto` after `wp_start` stops at the `GoAlloc ListNode (CompositeLiteral ...)`.
Must use explicit `wp_alloc newNode_loc as "Hnew"` + `iStructNamed "Hnew". simpl.`.
Then `wp_auto` continues to the if statement.

### early return / wp_if_destruct interaction
After the initial `wp_if_destruct` on `head == null`:
- True branch (head = null): goal is already `Φ (#newNode_loc)` — exception_do caught the return
- False branch (head ≠ null): goal is `WP exception_do (for: ...) {{v, Φ v}}` — the loop is still wrapped

In the false branch, `wp_auto` FAILS because exception_do wraps a non-straight-line (for loop).
Do NOT call `wp_auto` in the false branch before the loop.
Instead: go straight to invariant setup → `wp_for "IH"`.

### Loop invariant for InsertBack
Since the loop condition reads `cur.Next`, the invariant must expose `cur`'s struct fields directly:
```
∃ cur cur_val cur_nxt n_prefix S_prefix S_rest,
  "cur"    ∷ cur_ptr ↦ cur ∗
  "Hcv"    ∷ cur.[Val] ↦ cur_val ∗
  "Hcn"    ∷ cur.[Next] ↦ cur_nxt ∗
  "Hseg"   ∷ is_list_seg n_prefix head S_prefix cur ∗
  "Hrest"  ∷ is_list cur_nxt S_rest ∗
  "Hnv"    ∷ newNode_loc.[Val] ↦ v ∗
  "Hnn"    ∷ newNode_loc.[Next] ↦ null ∗
  "newNode"∷ newNode_ptr ↦ newNode_loc ∗
  "head"   ∷ head_ptr ↦ head ∗
  "%HS"    ∷ ⌜S = S_prefix ∪ {[cur_val]} ∪ S_rest⌝
```
All hypotheses (including newNode fields, stack pointers) must be in the invariant
because `wp_for` collects ALL spatial hypotheses via `iNamedAccu`.

### wp_if_destruct branch order for ≠ condition
Same as Contains: branch 1 = exit (cur_nxt = null), branch 2 = body (cur_nxt ≠ null).

### Loop exit reconstruction
After exit (cur_nxt = null) and `wp_auto` processing post-loop code:
- `wp_auto` handles: load newNode, load cur, store cur.Next=newNode, load head, return head
- After store: "Hcn" becomes cur.[Next] ↦ newNode_loc
- Goal becomes Φ (#head)
- Reconstruct: is_list_seg_snoc + is_list_seg_to_list + is_list newNode_loc {[v]}
- Need: replace ({[v]} ∪ S) with ((S_prefix ∪ {[cur_val]}) ∪ {[v]}) by set_solver

## Status
- [x] Contains proved (compiled)
- [ ] InsertBack — in progress, proof structure understood, compiling
- [ ] CopyList
- [ ] DeleteAll
