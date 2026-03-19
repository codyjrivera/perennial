# Proof Sketches for Linked List Methods

## 1. InsertFront

**What it does**: Creates a new ListNode with value `v` and `Next` pointing to `head`, returns the new node.

**Proof strategy**: Non-recursive, no case split needed on nil vs non-nil. Just unfold `is_list`, get the element list, allocate the new node, then reassemble `is_list` with `v :: elems`.

**Key steps**:
1. `wp_start as "Hlist".` to get the precondition
2. Unfold `is_list`: `iDestruct "Hlist" as (elems) "[%Hset Hlist_elems]".`
3. `wp_alloc l as "Hl". iStructNamed "Hl".` to get field pointsto for new node
4. `wp_auto.` to handle the remaining computation
5. `wp_end.` or `iApply "HΦ".`
6. Witness `v :: elems`, show `list_to_set (v :: elems) = {[v]} ∪ S` by `simpl; subst; done`
7. Provide the new `is_list_elems` by framing Val, Next pointsto and old list
