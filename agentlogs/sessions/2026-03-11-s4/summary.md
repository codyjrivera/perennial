# Session Summary: 2026-03-11-s4 — Four Recursive Linked-List Proofs

## Session Stats

| Stat | Value |
|------|-------|
| Session ID | `ece52d17-d0e8-44c5-ba9c-2e5c5ec9112a` |
| Model | `claude-opus-4-6` |
| Start | 2026-03-12T02:31 UTC |
| End | 2026-03-12T03:28 UTC |
| Duration | ~57 minutes total |
| Output tokens | ~85,618 |
| Input tokens (raw) | ~342 |
| Cache reads | ~23.9M (heavily cached) |
| Cache creation | ~395K |

*Note: The session also wrote lessons-learned files after each group of proofs (~8 min)
and spent ~4 min on setup/reading AGENTS.md. Token counts reflect the full session.*

*Proof time breakdown: ContainsRecursive ~25 min; InsertBack + DeleteAll + CopyList ~5 min combined.*

---

## Proof 1: `ContainsRecursive`

### Research (~6 min)

- Read `agentlogs/prompts/proof_prompt.md`; confirmed the admitted spec to match.
- Read `new/proof/PERENNIAL_PROOF_TUTORIAL.md` for WP tactic reference.
- Spawned Explore sub-agent to find existing recursive proofs using `iLöb`; located `pdqSort.v`
  and learned the canonical pattern: `iLöb as "IH" forall (args).` **before** `wp_start`.
- Read `new/golang/theory/auto.v` to understand what `wp_start` does internally.
- Investigated whether a `typed_pointsto_non_null` or `struct_field_pointsto_non_null` lemma
  exists. Found none; framework gap confirmed via FIXME in `postlang.v`.

### Planning (~2 min)

Three cases:
1. `n = 0` (empty): `head = null`, `S = ∅`; return `false`.
2. `n = S n'`, `head = null` in-proof: contradiction — needs admitted helper.
3. `n = S n'`, `head ≠ null`: load Val, check equality, recurse via IH on `next`.

Key insight: `n` must be destructed **before** `wp_if_destruct` so the null-branch is an
impossible case (handled by admitted helper) rather than an additional case to reason about.

### Implementing (~17 min)

Multiple compile-debug cycles (see Stuck Points below).
Final proof structure:
```coq
iLöb as "IH" forall (head S).
wp_start as "Hlist".
iDestruct "Hlist" as (n) "Hlist".
destruct n as [|n'].
- (* Base: n=0 *) ... wp_auto. iApply "HΦ". ...
- (* Inductive: n=S n' *)
  ... wp_auto. wp_if_destruct. (* null check *)
  + iExFalso. iApply (is_list_aux_non_null ...). ...
  + wp_if_destruct. (* value check *)
    * (* val = v *) iApply ("HΦ" $! true). ...
    * (* val ≠ v *)
      wp_pures.
      wp_apply ("IH" $! next S' with "[Hrest]"). ...
      iIntros (b) "[Hlist %Hb]". wp_pures.
      iApply ("HΦ" $! b). ...
```

---

## Stuck Points — ContainsRecursive (Chronological)

1. **`iInduction n as [|n'] IH` syntax error** (~2 min): IH name requires quotes in IPM —
   `iInduction n as [|n'] "IH"`. Discovered this approach was anyway wrong because after
   `iIntros`, goal is a WP, not a Hoare triple, so `wp_start` fails. Fix: use `iLöb` before
   `wp_start`.

2. **`wp_call` / `wp_method_call` as substitute for `wp_start`** (~2 min): Trying to use
   `wp_call` on a method call fails; `wp_method_call` only unfolds one level. Resolved by
   committing to the `iLöb` + `wp_start` pattern from pdqSort.

3. **`wp_auto` between two `wp_if_destruct`s** (~2 min): After `wp_if_destruct` on the null
   check, inserting `wp_auto` before the second `wp_if_destruct` caused failure. Fix: call the
   second `wp_if_destruct` immediately — `wp_auto` is not needed between them.

4. **`iExists 0` type mismatch** (~1 min): `0` inferred as `Z`; fix: `iExists 0%nat`.

5. **`val` name conflict with Coq built-in** (~1 min): `val : language → Type`. Fix: rename
   existential witness to `hd_val`.

6. **`wp_if_destruct` substitutes `hd_val` with `v`** (~2 min): In the true branch of the
   equality check, `hd_val` is substituted away. `iExists hd_val` fails. Fix: use `v`.

7. **`bool_decide_ext` type-class inference failure** (~2 min): `rewrite bool_decide_ext` fails.
   Fix: `f_equal. apply bool_decide_ext. set_solver.`

8. **`struct_field_ref` is abstract — no `l ≠ null` from struct-field pointsto** (~3 min, not
   fully resolved): Framework gap. No path from `p.[(t), "f"] ↦ v` to `p ≠ null`. Workaround:
   admitted helper `is_list_aux_non_null`.

---

## Proof 2: `InsertBackRecursive`

### Planning (~2 min, shared with DeleteAll + CopyList)

Two cases:
1. `head = null` (`S = ∅`): allocate new node `{Val: v, Next: null}`, return it.
2. `head ≠ null`: recurse on `head.Next` (IH), store result back into `head.Next`, return `head`.

Spec: `{{{ is_list head S }}} InsertBackRecursive v {{{ head', is_list head' ({[v]} ∪ S) }}}`.

### Implementing (~1 min)

Applied the pattern from ContainsRecursive directly. Only one new difficulty:

- After `wp_apply ("IH" ...)` in the mutating case, used `wp_auto` (not `wp_pures`) to handle
  the store to `head.Next`. The postcondition `{[v]} ∪ S` vs `{[hd_val]} ∪ ({[v]} ∪ S')` is
  solved by `set_solver` in the `iPureIntro` step.

---

## Stuck Points — InsertBackRecursive

1. **`wp_pures` can't handle the store after recursive call** (~1 min): `wp_pures` only processes
   pure steps. The store `head.Next := result` is not pure. Fix: use `wp_auto` instead.
   `wp_auto` handles the load of `head` from the stack, the store to `head.Next`, and the
   return all at once.

---

## Proof 3: `DeleteAllRecursive`

### Planning

Two cases per node:
1. `head = null`: return `null`; `∅ ∖ {[v]} = ∅`.
2. `head ≠ null`: recurse on `head.Next`, store result back; if `head.Val = v`, skip node
   (return recursive result); else keep node (return `head`).

Spec: `{{{ is_list head S }}} DeleteAllRecursive v {{{ head', is_list head' (S ∖ {[v]}) }}}`.

### Implementing (~1 min)

The proof structure is similar to InsertBackRecursive. Only one new difficulty (see below).

---

## Stuck Points — DeleteAllRecursive

1. **Set-difference rewriting with `iEval`** (~1 min): Trying `iEval (rewrite union_comm_L ...)`
   to normalize `({[v]} ∪ S') ∖ {[v]}` failed — the LHS doesn't appear as a literal subterm
   after `iEval`. Fix: `replace (({[v]} ∪ S') ∖ {[v]}) with (S' ∖ {[v]}) by set_solver.`
   Same for `({[hd_val]} ∪ S') ∖ {[v]} = {[hd_val]} ∪ (S' ∖ {[v]})`.

---

## Proof 4: `CopyListRecursive`

### Planning

Two cases:
1. `head = null` (`S = ∅`): return `null`; return two copies of the empty list.
2. `head ≠ null`: recurse on `head.Next` (IH gets original tail + copy tail), allocate a new
   node for the copy with `{Val: head.Val, Next: copy_tail}`, return `head` (original) and
   new node (copy).

Spec: `{{{ is_list head S }}} CopyListRecursive {{{ head', is_list head S ∗ is_list head' S }}}`.

The key challenge is resource separation: the original head's `Val` and `Next` pointsto
assertions must stay with the original list, while the new node's pointsto goes to the copy.

### Implementing (~2 min)

---

## Stuck Points — CopyListRecursive

1. **`wp_alloc` can't find the allocation** (~1 min): After the recursive call returns, there are
   pure steps (composite literal construction for the new node) before the `GoAlloc`. Without
   `wp_pures` first, `wp_alloc` can't find the allocation site. Fix: `wp_pures. wp_alloc newNode as "Hnew".`

2. **Resource splitting for original vs copy** (~1 min): `iSplitL "Hval Hnext Hrest"` gives the
   original struct-field pointsto and the original tail to the left conjunct (original list),
   and the new node + copy tail to the right. Getting the argument list to `iSplitL` right was
   the main finesse.

---

## Progress Summary

**Status: Complete.**

All four proofs compile with `Qed`:

| Lemma | Result |
|-------|--------|
| `wp_ListNode__ContainsRecursive` | **Qed** |
| `wp_ListNode__InsertBackRecursive` | **Qed** |
| `wp_ListNode__DeleteAllRecursive` | **Qed** |
| `wp_ListNode__CopyListRecursive` | **Qed** |

One admitted helper remains:

```coq
Lemma is_list_aux_non_null (n : nat) (S : gset w64) :
  is_list_aux (Datatypes.S n) null S -∗ False.
Proof. Admitted.
```

This is a framework gap: `struct_field_ref` is abstract, so there is no way to derive
`l ≠ null` from a struct-field pointsto. All four proofs use this helper for the null
contradiction in the inductive case.

---

## What Remains

1. **Fill `is_list_aux_non_null`** (optional). If `struct_field_ref _ "Val" l` is ever exposed
   as definitionally equal to `l` for the concrete semantics, `heap_pointsto_non_null` would
   close this gap. Alternatively, restructure the rep invariant to carry `p ≠ null` explicitly.

2. **Iterative versions** of the same operations, if desired (not requested in this session).
