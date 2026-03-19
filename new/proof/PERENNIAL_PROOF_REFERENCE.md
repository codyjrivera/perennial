# Perennial Proof Tactics — Detailed Reference

Detailed proof state examples and advanced patterns. For the concise tutorial,
see `PERENNIAL_PROOF_TUTORIAL.md`.

---

## WP Tactics — Detailed

### `wp_start`

**Syntax**: `wp_start as "ipat"` or `wp_start`

Begins a proof of a Hoare triple. It:
1. Introduces the postcondition continuation `Φ` as `"HΦ"`.
2. Introduces the precondition.
3. Automatically extracts and discards `is_pkg_init` facts (moving them to the
   persistent context).
4. Destructs the remaining precondition using the given intro pattern.
5. Unfolds the function/method being called and applies `wp_call`.

**Example**:
```coq
Lemma wp_Swap (l1 l2: loc) (x y: w64) :
  {{{ is_pkg_init heap ∗ l1 ↦ x ∗ l2 ↦ y }}}
    @! heap.Swap #l1 #l2
  {{{ RET #(); l1 ↦ y ∗ l2 ↦ x }}}.
Proof.
  wp_start as "[Hx Hy]".
  (* Now we have:
     "Hx": l1 ↦ x
     "Hy": l2 ↦ y
     "HΦ": ∀ v, l1 ↦ y ∗ l2 ↦ x -∗ Φ v
  *)
```

If the precondition is a pure fact, use `%`:
```coq
  wp_start as "%Hoverflow".
  (* Hoverflow is now a Rocq hypothesis, not an IPM hypothesis *)
```

**Proof state before `wp_start`**:
```
  ============================
  {{{ is_pkg_init heap ∗ l1 ↦ x ∗ l2 ↦ y }}}
    @!heap.Swap (# l1) (# l2)
  {{{ RET # (); l1 ↦ y ∗ l2 ↦ x }}}
```

**Proof state after `wp_start as "[Hx Hy]"`**:
```
  _ : is_pkg_init heap
  --------------------------------------□
  "Hx" : l1 ↦ x
  "Hy" : l2 ↦ y
  "HΦ" : l1 ↦ y ∗ l2 ↦ x -∗ Φ (# ()%V)
  --------------------------------------∗
  WP exception_do
       (let: "y" := GoAlloc (go.PointerType go.int) (# l2) in
        let: "x" := GoAlloc (go.PointerType go.int) (# l1) in
        ... )
  {{ v, Φ v }}
```

Note how `is_pkg_init` is in the persistent context (`□`), `"HΦ"` holds the
postcondition wand, and the goal is a WP over the function body (already
unfolded).

**Variant**: `wp_start_folded as "ipat"` — same but does NOT unfold the
function body. Useful when proving a spec that wraps another spec.

**Defined in**: `new/golang/theory/auto.v:40-67`

---

### `wp_auto`

**Syntax**: `wp_auto` or `wp_auto --lc n`

The workhorse tactic. Repeatedly applies:
1. `wp_pure` — pure computation steps (let bindings, arithmetic, pairs, etc.)
2. `wp_load` — loads from memory (when it finds a matching `l ↦ v` in context)
3. `wp_store` — stores to memory (when it finds a matching `l ↦ v` in context)
4. `wp_alloc_auto` — allocations with automatic naming

This handles the vast majority of straight-line code. It stops when it reaches
something it can't handle automatically (function calls, if expressions, loops,
etc.).

**When it gets stuck**: If `wp_auto` can't make progress, you likely need one of:
- `wp_if_destruct` — for conditionals
- `wp_apply` — for function/method calls
- `wp_for` — for loops
- `wp_alloc l as "H"` — for allocations that need specific names

**Proof state before `wp_auto`** (continuing the Swap example):
```
  "Hx" : l1 ↦ x
  "Hy" : l2 ↦ y
  "HΦ" : l1 ↦ y ∗ l2 ↦ x -∗ Φ (# ()%V)
  --------------------------------------∗
  WP exception_do
       (let: "y" := GoAlloc (go.PointerType go.int) (# l2) in
        let: "x" := GoAlloc (go.PointerType go.int) (# l1) in
        let: "old_y" := GoAlloc go.int (GoZeroVal go.int (# ()%V)) in
        let: "$r0" := ![go.int] ![go.PointerType go.int] "y" in
        (do: "old_y" <-[go.int] "$r0") ;;;
        let: "$r0" := ![go.int] ![go.PointerType go.int] "x" in
        (do: ![go.PointerType go.int] "y" <-[go.int] "$r0") ;;;
        let: "$r0" := ![go.int] "old_y" in
        (do: ![go.PointerType go.int] "x" <-[go.int] "$r0") ;;;
        return: # ()%V)
  {{ v, Φ v }}
```

**Proof state after `wp_auto`**:
```
  "Hx" : l1 ↦ y       (* NOTE: updated by store *)
  "Hy" : l2 ↦ x       (* NOTE: updated by store *)
  "HΦ" : l1 ↦ y ∗ l2 ↦ x -∗ Φ (# ()%V)
  --------------------------------------∗
  Φ (# ()%V)
```

`wp_auto` processed all allocations, loads, and stores in one step. The
points-to hypotheses are updated to reflect the swapped values, and the
program has been fully executed down to the return value.

**The `--lc` parameter**: `wp_auto --lc 2` generates 2 later credits during
pure steps. Rarely needed.

**Defined in**: `new/golang/theory/auto.v:87-169`

---

### `wp_pure` / `wp_pures`

`wp_pure` takes a single pure computation step (function application, let
binding, pair construction, fst/snd, arithmetic, if with literal bool, etc.).
`wp_pures` repeats `wp_pure` until it can't make progress.

Building blocks of `wp_auto`. Useful for debugging when `wp_auto` gets stuck.

Pure steps are defined via the `PureWp` typeclass.

**Defined in**: `new/golang/theory/proofmode.v:254-256`

---

### `wp_call`

Handles a function application `(rec: f x := body) v` by substituting the
argument. Called automatically by `wp_start` and `wp_pures`.

**Variant**: `wp_call_lc "Hlc"` — keeps the later credit.

**Defined in**: `new/golang/theory/proofmode.v:275-276`

---

### `wp_bind`

**Syntax**: `wp_bind e` or `wp_bind`

Applies the bind rule to focus on a subexpression `e`. The goal changes from
`WP K[e] {{ Φ }}` to `WP e {{ v, WP K[v] {{ Φ }} }}`.

Without an argument, finds the next interesting subexpression automatically.
You rarely need this directly — `wp_apply` calls it automatically.

**Defined in**: `new/golang/theory/proofmode.v:299-358`

---

### `wp_apply`

**Syntax**: `wp_apply (lemma with "spat")` or `wp_apply lemma as "ipat"`

The primary way to use a previously-proven specification. Combines
`wp_bind` + `iApply`. It:
1. Finds the next function call in the goal.
2. Applies the bind rule to focus on it.
3. Applies the given lemma.
4. Automatically handles `is_pkg_init` in the precondition.
5. Optionally runs `wp_auto` on the remaining goal.

**Specialization patterns** (`with`):
```coq
wp_apply (wp_Mutex__Lock with "[$Hlock]").
(* [$Hlock] means: frame Hlock into the precondition automatically *)

wp_apply (wp_slice_append with "[$Hels $Hels_cap $Hs_tmp]").
(* Multiple hypotheses framed in *)
```

**Intro patterns** (`as`):
```coq
wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hinv]".
wp_apply wp_map_make1 as "%mref Hm".
```

**Optional parameters**:
- `--no-auto` — don't run `wp_auto` afterward
- `--lc n` — generate `n` later credits

**Defined in**: `new/golang/theory/auto.v:182-214`

---

### `wp_alloc`

**Syntax**: `wp_alloc l as "H"`

Handles a `GoAlloc` expression. Introduces a fresh location `l` and a
points-to fact named `"H"`. Inside `wp_auto`, allocations are handled
automatically with names derived from the Go variable name (e.g., Go variable
`x` becomes Rocq variable `x_ptr` with hypothesis `"x"`).

**When to use explicitly**: When automatic naming conflicts with an existing
name, or when you need a specific name.

**Defined in**: `new/golang/theory/mem.v:219-222`

---

### `wp_load` / `wp_store`

Handles a load (`GoLoad`) or store (`GoStore`) by finding a matching `l ↦ v`
in context. For stores, the points-to is updated. Both called automatically by
`wp_auto`.

**Defined in**: `new/golang/theory/mem.v:224-225`

---

### `wp_if_destruct`

When the goal contains `if: #b then ... else ...`, case-splits on `b`. Creates
two subgoals with the condition fact added to each. Runs `wp_pures` to step
into the appropriate branch.

**Example**:
```coq
  (* Goal has: if: #(bool_decide (uint.Z x < uint.Z y)) then ... else ... *)
  wp_if_destruct.
  - (* Branch: uint.Z x < uint.Z y *)
    ...
  - (* Branch: ¬ (uint.Z x < uint.Z y) *)
    ...
```

**Proof state example** (Fibonacci, after `wp_if_destruct` on `n == 0`):

Goal 1 (true branch, `n = W64 0`):
```
  Hoverflow : fibonacci (uint.nat (W64 0)) < 2 ^ 64
  --------------------------------------□
  "HΦ" : ∀ c : w64, ⌜uint.nat c = fibonacci (uint.nat (W64 0))⌝ -∗ Φ (# c)
  --------------------------------------∗
  Φ (# (W64 0))
```

Goal 2 (false branch, `n ≠ W64 0`):
```
  n0 : n ≠ W64 0
  "HΦ" : ∀ c : w64, ⌜uint.nat c = fibonacci (uint.nat n)⌝ -∗ Φ (# c)
  "n" : n_l ↦ n
  "fib_prev" : fib_prev_ptr ↦ W64 0
  "fib_cur" : fib_cur_ptr ↦ W64 1
  "i" : i_ptr ↦ W64 1
  --------------------------------------∗
  WP exception_do (for: ... ) {{ v, Φ v }}
```

Note how `wp_if_destruct` substituted `n = W64 0` in the first branch and
added `n0 : n ≠ W64 0` in the second.

**Defined in**: `new/golang/theory/auto.v:321-342`

---

### `wp_for`

**Syntax**: `wp_for` or `wp_for "IH"`

Handles a `for: cond; post := body` loop. The typical pattern is:

1. State a loop invariant with `iAssert`.
2. Apply `wp_for` which sets up the induction.

The tactic:
1. Binds the `do_for` expression.
2. Applies the `wp_for` lemma, which requires proving:
   - The invariant holds initially (discharged by `iNamedAccu`).
   - Under the invariant, the loop condition produces either `#true` (then prove
     the body preserves the invariant) or `#false` (then prove the
     postcondition).

With `wp_for "IH"`, the invariant is automatically destructed using
`iNamed "IH"`.

**Example**:
```coq
  iAssert (∃ (i prev cur: w64),
    "fib_prev" ∷ fib_prev_ptr ↦ prev ∗
    "fib_cur" ∷ fib_cur_ptr ↦ cur ∗
    "i" ∷ i_ptr ↦ i ∗
    "%Hprev" ∷ ⌜uint.nat prev = fibonacci (uint.nat i - 1)⌝ ∗
    "%Hcur" ∷ ⌜uint.nat cur = fibonacci (uint.nat i)⌝
  )%I with "[$i $fib_prev $fib_cur]" as "IH".
  { (* Prove invariant holds initially *) ... }
  wp_for; iNamed "IH"; wp_auto.
  - (* Loop body: condition was true *)
    ...
    wp_for_post.
    (* Prove invariant is restored *)
    ...
  - (* Loop exit: condition was false *)
    wp_end.
    ...
```

**Proof state after `iAssert` (before `wp_for`)**:
```
  "HΦ" : ∀ c : w64, ⌜uint.nat c = fibonacci (uint.nat n)⌝ -∗ Φ (# c)
  "n" : n_l ↦ n
  "IH" : ∃ i prev cur : w64,
           "fib_prev" ∷ fib_prev_ptr ↦ prev ∗
           "fib_cur" ∷ fib_cur_ptr ↦ cur ∗
           "i" ∷ i_ptr ↦ i ∗
           "%Hi_ge" ∷ ⌜1 ≤ uint.Z i ≤ uint.Z n⌝ ∗ ...
  --------------------------------------∗
  WP exception_do (for: ... ) {{ v, Φ v }}
```

**Proof state after `wp_for; iNamed "IH"; wp_auto`**:
```
  i, prev, cur : w64
  Hi_ge : 1 ≤ uint.Z i ≤ uint.Z n
  Hprev : uint.nat prev = fibonacci (uint.nat i - 1)
  Hcur : uint.nat cur = fibonacci (uint.nat i)
  "HΦ" : ∀ c : w64, ⌜...⌝ -∗ Φ (# c)
  "n" : n_l ↦ n
  "fib_prev" : fib_prev_ptr ↦ prev
  "fib_cur" : fib_cur_ptr ↦ cur
  "i" : i_ptr ↦ i
  --------------------------------------∗
  if decide (# (bool_decide (uint.Z i < uint.Z n)) = # true)
  then WP body {{ for_postcondition ... }}
  else Φ execute_val
```

The `iNamed` has destructed the existentials and named propositions. The goal
is now an `if decide` — use `wp_if_destruct` (or `destruct (decide _)`) to
split into the loop body (true) and exit (false) cases.

**Defined in**: `new/golang/theory/auto.v:302-305`, `new/golang/theory/loop.v:175-178`

---

### `wp_for_post`

When the goal is a `for_postcondition`, automatically applies the correct
lemma based on how the loop body terminates:
- `wp_for_post_do` — normal execution (falls through to post-statement)
- `wp_for_post_continue` — `continue` statement
- `wp_for_post_break` — `break` statement
- `wp_for_post_return` — `return` statement

After applying the lemma, tries `wp_auto`.

**Defined in**: `new/golang/theory/auto.v:306-307`, `new/golang/theory/loop.v:181-193`

---

### `wp_end`

Finishes a proof branch by:
1. Running `wp_pures`.
2. Introducing any modalities with `iModIntro`.
3. Applying `"HΦ"` (or `"HPost"`) to prove the postcondition.
4. Attempting `auto; iFrame; word` to solve the resulting goal.

If it fails, do `iApply "HΦ"` manually and prove the postcondition step by
step.

**Defined in**: `new/golang/theory/auto.v:365-381`

---

### `wp_if_join`

**Syntax**: `wp_if_join asn` or `wp_if_join asn with "spat"`

For an `if: #b then e1 else e2` where both branches return a value (rather
than diverging control flow), this joins the two branches into a common
assertion `asn`. Creates three subgoals:
1. Prove `asn` in the true branch.
2. Prove `asn` in the false branch (generated by `wp_if_destruct`).
3. Continue the proof with `asn` as an assumption.

**Defined in**: `new/golang/theory/auto.v:358-363`

---

## Recursive Functions — `iLöb`

### Overview

Go functions that call themselves require **Löb induction** (`iLöb`) to prove in
Perennial. The key rule: **`iLöb` must come before `wp_start`**.

After `wp_start` the goal is a WP (`WP expr {{ Φ }}`), not a Hoare triple. `iLöb`
operates on Hoare triples; calling it after `wp_start` will fail or produce the
wrong IH. Similarly, `iInduction` + manual `iIntros` fails because `wp_start` then
can't find its Hoare triple.

### Syntax

```coq
iLöb as "IH" forall (head S).
```

- `"IH"` — name for the induction hypothesis (an IPM hypothesis, so it needs quotes)
- `forall (head S)` — generalize over variables that change in each recursive call;
  anything not generalized is fixed for the entire induction

### Proof state

**Before `iLöb`**:
```
============================
{{{ is_pkg_init pkg ∗ is_list head S }}}
  head @! (go.PointerType pkg.Node) @! "MyMethod" #arg
{{{ (r : T), RET #r; Q head S r }}}
```

**After `iLöb as "IH" forall (head S)`**:
```
"IH" : ∀ (head : loc) (S : gset w64),
         {{{ is_pkg_init pkg ∗ is_list head S }}}
           head @! (go.PointerType pkg.Node) @! "MyMethod" #arg
         {{{ (r : T), RET #r; Q head S r }}}
-------------------------------∗
{{{ is_pkg_init pkg ∗ is_list head S }}}
  head @! (go.PointerType pkg.Node) @! "MyMethod" #arg
{{{ (r : T), RET #r; Q head S r }}}
```

The IH is a Hoare triple in the IPM context. Apply it with:

```coq
wp_apply ("IH" $! next_head next_S with "[resources]").
{ iFrame "#". iExists n'. iFrame. }
iIntros (result) "Hpost".
```

The `$!` splat is how you instantiate the `forall` arguments. Resources for the
precondition go in `with "[...]"`.

### Full skeleton for recursive linked-list methods

```coq
Proof.
  iLöb as "IH" forall (head S).
  wp_start as "Hlist".
  iDestruct "Hlist" as (n) "Hlist".
  destruct n as [|n'].
  - (* Base: head = null, S = ∅ *)
    iDestruct "Hlist" as "[%Hnull %Hempty]". subst.
    wp_auto.
    iApply "HΦ". (* construct postcondition for empty case *) ...
  - (* Inductive: n = S n' *)
    simpl.
    iDestruct "Hlist" as (hd_val next S') "(%Heq & Hval & Hnext & Hrest)". subst.
    wp_auto.             (* handles loads, stops before first if *)
    wp_if_destruct.      (* null check *)
    + (* head = null — contradiction in inductive case *)
      iExFalso.
      iApply (is_list_aux_non_null n' _).
      simpl. iExists hd_val, next, S'. iFrame. iPureIntro. done.
    + (* head ≠ null — main case *)
      wp_pures.          (* or omit, depending on context *)
      wp_apply ("IH" $! next S' with "[Hrest]").
      { iFrame "#". iExists n'. iFrame. }
      iIntros (...) "...".
      wp_auto.           (* wp_pures if no stores follow *)
      iApply "HΦ". (* reconstruct is_list for next case *) ...
Qed.
```

### `wp_auto` vs `wp_pures` after the recursive call

| Situation | Tactic |
|:--|:--|
| Read-only recursive call (Contains, Copy source side) | `wp_pures` |
| Mutating recursive call (InsertBack, DeleteAll) — a store to a field follows | `wp_auto` |

`wp_pures` can't handle stores. `wp_store` fails when loads precede the store that
it can't see past. `wp_auto` handles the full load-store-return sequence in one go.

### Null contradiction in the inductive case

`struct_field_ref` is an abstract typeclass; there is no general lemma deriving
`l ≠ null` from a struct-field points-to `l.[T, "f"] ↦ v`. When your rep invariant
has `Datatypes.S n` nodes but `wp_if_destruct` still creates a `head = null` branch,
the right workaround is an admitted helper:

```coq
Lemma is_list_aux_non_null (n : nat) (S : gset w64) :
  is_list_aux (Datatypes.S n) null S -∗ False.
Proof. Admitted.
(* Framework gap: struct_field_ref is abstract, so heap_pointsto_non_null
   doesn't apply to struct field points-to. Would be closed if struct_field_ref
   were exposed as definitionally equal to the field offset for concrete types. *)
```

---

## Struct Tactics — Detailed

### `iStructNamed`

**Syntax**: `iStructNamed "H"`

Splits a struct points-to `l ↦ struct_val` into individual field points-to
facts. Each field gets a name derived from the Go field name.

```coq
wp_alloc l as "H".
iStructNamed "H". simpl.
(* Now have individual field hypotheses like:
   "x" : l.[MyStruct.t, "x"] ↦ x_val
   "y" : l.[MyStruct.t, "y"] ↦ y_val
*)
```

**Proof state before `iStructNamed`** (for `AtomicInt` with fields `x`, `mu`):
```
  "Hint" : l ↦ {| concurrent.AtomicInt.x' := W64 0;
                   concurrent.AtomicInt.mu' := m_ptr |}
  --------------------------------------∗
  WP ... {{ v, Φ v }}
```

**Proof state after `iStructNamed "Hint". simpl.`**:
```
  "x" : l.[concurrent.AtomicInt.t, "x"] ↦ W64 0
  "mu" : l.[concurrent.AtomicInt.t, "mu"] ↦ m_ptr
  --------------------------------------∗
  WP ... {{ v, Φ v }}
```

### `iStructNamedPrefix`

**Syntax**: `iStructNamedPrefix "H" "prefix"`

Like `iStructNamed` but prefixes each field name. Useful to avoid name clashes.

```coq
iStructNamedPrefix "Hptr" "H".
(* Fields named "Hx", "Hy", etc. *)
```

### `iPersist`

**Syntax**: `iPersist "H"` or `iPersist "H" as "H2"`

Moves a hypothesis to the persistent (intuitionistic) context, marked with `□`.
Useful for immutable field points-to facts (`l.[S, "f"] ↦□ v`).

**Proof state before `iPersist "mu"`**:
```
  "x" : l.[concurrent.AtomicInt.t, "x"] ↦ W64 0
  "mu" : l.[concurrent.AtomicInt.t, "mu"] ↦ m_ptr
  --------------------------------------∗
  ...
```

**Proof state after `iPersist "mu"`**:
```
  "mu" : l.[concurrent.AtomicInt.t, "mu"] ↦□ m_ptr
  --------------------------------------□
  "x" : l.[concurrent.AtomicInt.t, "x"] ↦ W64 0
  --------------------------------------∗
  ...
```

---

## IPM Tactics — Detailed

### Introduction and Destruction

| Tactic | Description |
|:--|:--|
| `iIntros "ipat"` | Introduce from goal (wands, universal quantifiers) |
| `iIntros (x y)` | Introduce Rocq-level variables |
| `iDestruct "H" as "ipat"` | Destruct a hypothesis |
| `iDestruct "H" as (x) "ipat"` | Destruct existential, binding `x` |
| `iNamed "H"` | Destruct using names from `∷` notation (named props) |
| `iNamedSuffix "H" "_sfx"` | Like `iNamed` but adds suffix to all names |
| `iClear "H"` | Remove a hypothesis |
| `iRename "H1" into "H2"` | Rename a hypothesis |

### Introduction patterns (ipat)

| Pattern | Meaning |
|:--|:--|
| `"H"` | Name the hypothesis `H` |
| `"[H1 H2]"` | Destruct `∗` (separating conjunction) |
| `"[H1 \| H2]"` | Destruct `∨` (disjunction) |
| `"(H1 & H2 & H3)"` | Nested destruction (sugar for `[H1 [H2 H3]]`) |
| `"%H"` | Move pure fact `⌜P⌝` to Rocq context as `H` |
| `"#H"` | Move to persistent context |
| `"$"` | Immediately frame with goal |
| `"_"` | Discard |
| `"-"` | Clear the hypothesis |
| `"!>"` | Introduce a modality (`iModIntro`) |
| `">H"` | Strip a later `▷` |

### Splitting and Framing

| Tactic | Description |
|:--|:--|
| `iSplitL "H1 H2"` | Split `∗` goal, give named hyps to left |
| `iSplitR "H1 H2"` | Split `∗` goal, give named hyps to right |
| `iFrame` | Automatically cancel matching hypotheses with goal |
| `iFrame "H"` | Frame specific hypothesis |
| `iFrame "#"` | Frame all persistent hypotheses |
| `iFrame "#∗"` | Frame persistent and spatial hypotheses |

### Application

| Tactic | Description |
|:--|:--|
| `iApply "H"` | Apply wand/implication hypothesis |
| `iApply (lem with "spat")` | Apply lemma with specialization pattern |
| `iExact "H"` | Exact match (like Rocq's `exact`) |
| `iExactEq "H"` | Match up to equality |
| `iAssumption` | Find a matching hypothesis |

### Specialization patterns (spat)

| Pattern | Meaning |
|:--|:--|
| `"[H1 H2]"` | Give H1 and H2 to the premise |
| `"[$]"` | Auto-frame everything possible |
| `"[$H1 H2]"` | Auto-frame H1, give H2 |
| `"[H1 $H2]"` | Give H1, auto-frame H2 |

### Existentials and Pure Facts

| Tactic | Description |
|:--|:--|
| `iExists x` | Provide witness for existential |
| `iPureIntro` | Switch to proving a pure `⌜P⌝` in Rocq |
| `iAssert P with "spat" as "ipat"` | Assert intermediate `P` |

### Modalities

| Tactic | Description |
|:--|:--|
| `iModIntro` | Introduce a modality (`▷`, `|==>`, etc.) |
| `iMod "H"` | Eliminate a fancy update `\|={E1,E2}=>` |
| `iMod "H" as "ipat"` | Eliminate and destruct |
| `iInv "H" as "ipat" "Hclose"` | Open an invariant |
| `iNext` | Strip later from goal |

### Ghost State

| Tactic | Description |
|:--|:--|
| `iMod (ghost_var_alloc x) as (γ) "[H1 H2]"` | Allocate ghost variable |
| `iDestruct (ghost_var_agree with "H1 H2") as %->` | Prove ghost vars agree |
| `iMod (ghost_var_update_2 v with "H1 H2") as "[H1 H2]"` | Update ghost var |
| `iCombine "H1 H2" as "H"` | Combine fractional resources |

---

## Specification Lemmas — Detailed

### Synchronization

| Lemma | Description |
|:--|:--|
| `wp_Mutex__Lock` | `{{{ is_Mutex l P }}} Lock {{ Hlocked ∗ P }}` |
| `wp_Mutex__Unlock` | `{{{ is_Mutex l P ∗ Hlocked ∗ P }}} Unlock {{ True }}` |
| `init_Mutex` | Initialize a mutex with its invariant |
| `wp_Mutex__TryLock` | Try to acquire lock (returns bool) |
| `wp_Cond__Wait` | Wait on condition variable |
| `wp_Cond__Signal` | Signal condition variable |
| `wp_Cond__Broadcast` | Broadcast condition variable |
| `wp_WaitGroup__Add` | Add to wait group counter |
| `wp_WaitGroup__Done` | Decrement wait group counter |
| `wp_WaitGroup__Wait` | Wait for counter to reach zero |

### Slices

| Lemma | Description |
|:--|:--|
| `wp_slice_literal` | Create a slice from a literal |
| `wp_slice_append` | Append element(s) to a slice |
| `wp_load_slice_index` | Load element at index |
| `wp_store_slice_index` | Store element at index |
| `wp_load_slice_elem` | Load slice element (variant) |
| `wp_store_slice_elem` | Store slice element (variant) |
| `own_slice_len` | Relate `slice.len s` to `length xs` |
| `own_slice_wf` | Slice well-formedness (len ≤ cap) |

### Maps

| Lemma | Description |
|:--|:--|
| `wp_map_make1` / `wp_map_make2` | Create a new map |
| `wp_map_insert` | Insert key-value pair |
| `wp_map_lookup2` | Look up a key |
| `wp_map_delete` | Delete a key |

### Goroutines

| Lemma | Description |
|:--|:--|
| `std.wp_Spawn` | Spawn a goroutine, get `JoinHandle` |
| `wp_JoinHandle__Join` | Wait for goroutine to finish |

### Assertions

| Lemma | Description |
|:--|:--|
| `wp_Assert` | `Assert(b)` — requires `b = true` |
| `wp_AngelicExit` | Unreachable code (angelic nondeterminism) |

---

## Advanced Proof Patterns

### Using a mutex

```coq
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hinv]".
  iNamed "Hinv".
  (* ... critical section ... *)
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP Hx]").
  { iFrame. }  (* re-prove lock invariant *)
```

### Spawning a goroutine

```coq
  wp_apply (std.wp_Spawn (postcondition) with "[resources_for_goroutine]").
  { (* Prove goroutine body *)
    iIntros (Φ) "HΦ".
    wp_auto.
    ...
    iApply "HΦ". iFrame. }
  iIntros (h) "Hh".
  (* ... do other work ... *)
  wp_apply (wp_JoinHandle__Join with "[$Hh]") as "Hresult".
```

### Ghost state pattern

```coq
  (* Allocate ghost variable *)
  iMod (ghost_var_alloc initial_val) as (γ) "[Hauth Hfrag]".
  (* Later, prove agreement *)
  iDestruct (ghost_var_agree with "Hauth Hfrag") as %->.
  (* Update ghost variable *)
  iMod (ghost_var_update_2 new_val with "Hauth Hfrag") as "[Hauth Hfrag]".
  { rewrite Qp.half_half //. }
```

### Invariant pattern

```coq
  (* Allocate invariant *)
  iMod (inv_alloc N _ (my_inv_body) with "[resources]") as "#Hinv".
  { iModIntro. iFrame "∗#". }
  (* Open invariant *)
  iInv "Hinv" as ">HI" "Hclose".
  iNamed "HI".
  (* ... do work ... *)
  (* Close invariant *)
  iMod ("Hclose" with "[resources_to_put_back]").
  { iModIntro. iFrame "∗#". }
```

### Named propositions (∷ notation)

The `∷` notation from `iris_named_props` names individual conjuncts for use
with `iNamed`:

```coq
Definition my_inv l : iProp Σ :=
  ∃ (x: w64),
    "Hx" ∷ l ↦ x ∗
    "%Hbound" ∷ ⌜uint.Z x < 100⌝.

(* In proof: *)
iNamed "Hinv".
(* Now have: "Hx": l ↦ x  and  Hbound: uint.Z x < 100 *)
```

Pure facts (prefixed with `%`) are automatically moved to the Rocq context.

---

## Tactic Source Locations

| Tactic | File |
|:--|:--|
| `wp_start` | `new/golang/theory/auto.v:40-67` |
| `wp_auto` | `new/golang/theory/auto.v:87-169` |
| `wp_pure`, `wp_pures` | `new/golang/theory/proofmode.v:254-256` |
| `wp_call` | `new/golang/theory/proofmode.v:275-276` |
| `wp_bind` | `new/golang/theory/proofmode.v:299-358` |
| `wp_apply` (basic) | `new/golang/theory/proofmode.v:380-386` |
| `wp_apply` (full) | `new/golang/theory/auto.v:198-214` |
| `wp_alloc` | `new/golang/theory/mem.v:219-222` |
| `wp_load`, `wp_store` | `new/golang/theory/mem.v:224-225` |
| `wp_if_destruct` | `new/golang/theory/auto.v:321-342` |
| `wp_for` | `new/golang/theory/auto.v:302-305` |
| `wp_for` (core) | `new/golang/theory/loop.v:175-178` |
| `wp_for_post` | `new/golang/theory/auto.v:306-307` |
| `wp_end` | `new/golang/theory/auto.v:365-381` |
| `wp_if_join` | `new/golang/theory/auto.v:358-363` |
| `PureWp` class | `new/golang/theory/proofmode.v:17-21` |
| `tac_wp_load` | `new/golang/theory/mem.v:93-112` |
| `tac_wp_store` | `new/golang/theory/mem.v:114-129` |
| `tac_wp_alloc` | `new/golang/theory/mem.v:131-141` |
