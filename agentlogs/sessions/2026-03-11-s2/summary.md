# Session Summary: 2026-03-11-s2 — ContainsRecursive

## Session Stats

| Stat | Value |
|------|-------|
| Session ID | `ccaf4b35-0aa8-459d-a16c-88f5303a9a42` |
| Model | `claude-opus-4-6` |
| Start | 2026-03-11 19:31 UTC |
| End | 2026-03-11 20:16 UTC |
| Duration | ~45 minutes total; ~22 min on ContainsRecursive |
| Output tokens | ~81,877 (whole session) |
| Input tokens (raw) | ~14,155 (whole session) |
| Tokens incl. cache reads | ~16.5M (heavily cached) |

*Note: The session also proved InsertFront (~8 min) before starting ContainsRecursive.*

---

## Work Breakdown (ContainsRecursive)

### Research (~8 min)
- Spawned Explore agents to find recursive proof examples using `iLöb` (`primitive.v`, `pdqsort.v`).
- Learned the `iLöb as "IH" forall ... "..."` and `wp_apply ("IH" with "[$]")` patterns.
- Investigated whether a `typed_pointsto_non_null` or `struct_field_pointsto_non_null` lemma exists for deriving `l ≠ null` from a struct field pointsto at `l`. Found none.
- Discovered a FIXME comment in the framework: `struct_field_ref` is abstract, making such a lemma unavailable without additional admitted axioms.

### Planning (~4 min)
- ContainsRecursive is recursive → `iLöb` required. Three cases:
  1. `n = 0` (empty list, `head = null`): return `false`, set is empty.
  2. `n > 0`, `head = null` in-proof: contradiction (framework gap — needs admitted helper).
  3. `n > 0`, `head ≠ null`: check Val, return `true` or recurse via `IH`.

### Implementing (~22 min, incomplete)
Multiple compile-debug cycles. See stuck points below.

---

## Stuck Points (Chronological)

1. **`iExists 0` type mismatch** (minor, ~2 min): `0` inferred as `Z` instead of `nat`. Fixed with `iExists 0%nat`.

2. **`wp_auto` fails to progress in non-empty branch** (~5 min): `wp_auto` couldn't step past the null comparison without knowing `head ≠ null`. Resolved by restructuring: use `wp_if_destruct` for the null check first, then case-split on `n` inside each branch.

3. **No lemma to derive `l ≠ null` from struct field pointsto** (~10 min): `heap_pointsto_non_null` exists only for raw `heap_pointsto`; `struct_field_ref` is abstract so no analogous lemma is derivable for struct fields. Worked around by adding an admitted helper:
   ```coq
   Lemma is_list_aux_null_inv n S :
     is_list_aux (Datatypes.S n) null S -∗ False.
   Proof. Admitted.
   ```

4. **`exception_do (return: ...)` wrapper blocks `wp_apply "IH"`** (~10 min, *unresolved*): After `wp_if_destruct` in the `Val ≠ v` branch, the goal is `WP exception_do (return: ...)`. The IH also wraps `exception_do`, but `wp_apply "IH"` fails to unify. Tried: `wp_pures` before apply, `wp_bind (next @! ...)` (caused focus error), manual unsealing. Session hit a usage limit before this was resolved.

---

## Progress Summary

**Status**: Incomplete.

Proof structure is laid out with `iLöb`. Two of three cases are handled:
- Base case (empty list) ✓
- Null contradiction in non-empty case ✓ (with admitted helper)
- Recursive call branch ✗ — blocked on `exception_do`/`return:` wrapping

**Admitted lemma** left in file:
```coq
Lemma is_list_aux_null_inv n S :
  is_list_aux (Datatypes.S n) null S -∗ False.
Proof. Admitted.
```

---

## What Remains

1. **Resolve `exception_do (return: ...)` in the recursive call branch.** Likely fix: use `wp_bind` to expose the inner recursive call before applying `IH`, or find a `wp_` lemma that steps through `exception_do`. Check other recursive proofs in the codebase that use `return:`.

2. **Fill in or eliminate `is_list_aux_null_inv`.** Could be eliminated by restructuring so `n` is destructed before `wp_if_destruct`, ensuring the null branch only arises when `n = 0` (where `is_list_aux` directly gives `head = null`).
