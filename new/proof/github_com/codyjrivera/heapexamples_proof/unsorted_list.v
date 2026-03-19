From New.generatedproof.github_com.codyjrivera Require Import heapexamples.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : heapexamples.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) heapexamples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) heapexamples := build_get_is_pkg_init_wf.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(* Rep invariant: gset-based, with n decoupled from size S.
   This allows duplicates in the linked list. *)
Fixpoint is_list_aux (n : nat) (p : loc) (S : gset w64) : iProp Σ :=
  match n with
  | O => ⌜p = null⌝ ∗ ⌜S = ∅⌝
  | Datatypes.S n' =>
    ∃ (v : w64) (next : loc) (S' : gset w64),
      ⌜S = {[v]} ∪ S'⌝ ∗
      p.[(heapexamples.ListNode.t), "Val"] ↦ v ∗
      p.[(heapexamples.ListNode.t), "Next"] ↦ next ∗
      is_list_aux n' next S'
  end.

Definition is_list (p : loc) (S : gset w64) : iProp Σ :=
  ∃ n, is_list_aux n p S.

(* Old list-based version (kept for reference):
 *
 * Fixpoint is_list_elems (p : loc) (elems : list w64) : iProp Σ :=
 *   match elems with
 *   | [] => ⌜p = null⌝
 *   | v :: rest =>
 *     ∃ (next : loc),
 *       "Val" ∷ p.[(heapexamples.ListNode.t), "Val"] ↦ v ∗
 *       "Next" ∷ p.[(heapexamples.ListNode.t), "Next"] ↦ next ∗
 *       is_list_elems next rest
 *   end.
 *
 * Definition is_list (p : loc) (S : gset w64) : iProp Σ :=
 *   ∃ (elems : list w64), ⌜list_to_set elems = S⌝ ∗ is_list_elems p elems.
 *)

Lemma wp_ListNode__InsertFront (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "InsertFront" #v
  {{{ (head' : loc), RET #head'; is_list head' ({[v]} ∪ S) }}}.
Proof.
  wp_start as "Hlist".
  wp_auto.
  wp_alloc head' as "Hnode".
  wp_auto.
  iApply "HΦ".
  iStructNamed "Hnode". simpl.
  iDestruct "Hlist" as (n) "Hlist".
  iExists (Datatypes.S n).
  simpl.
  iExists v, head, S.
  iFrame.
  iPureIntro. done.
Qed.

(* Framework gap: struct_field_ref is abstract, so there is no general lemma
   deriving l ≠ null from a struct-field pointsto at l. In the concrete Go
   semantics, the first field of any struct sits at offset 0, so
   struct_field_ref _ "Val" l = l and heap_pointsto_non_null gives l ≠ null.
   Admitted until the framework exposes this. *)
Lemma is_list_aux_non_null (n : nat) (S : gset w64) :
  is_list_aux (Datatypes.S n) null S -∗ False.
Proof. Admitted.

Lemma wp_ListNode__ContainsRecursive (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "ContainsRecursive" #v
  {{{ (b : bool), RET #b; is_list head S ∗ ⌜b = bool_decide (v ∈ S)⌝ }}}.
Proof.
  iLöb as "IH" forall (head S).
  wp_start as "Hlist".
  iDestruct "Hlist" as (n) "Hlist".
  destruct n as [|n'].
  - (* Base case: n = 0, head = null, S = ∅ *)
    iDestruct "Hlist" as "[%Hnull %Hempty]". subst.
    wp_auto.
    iApply "HΦ". iSplitL.
    + iExists 0%nat. simpl. iPureIntro. done.
    + iPureIntro. rewrite bool_decide_eq_false_2; first done.
      set_solver.
  - (* Inductive case: n = S n' *)
    simpl.
    iDestruct "Hlist" as (hd_val next S') "(%Heq & Hval & Hnext & Hrest)". subst.
    wp_auto.
    wp_if_destruct.
    + (* head = null, contradiction *)
      iExFalso.
      iApply (is_list_aux_non_null n' ({[hd_val]} ∪ S')).
      simpl. iExists hd_val, next, S'. iFrame. iPureIntro. done.
    + wp_if_destruct.
      * (* val = v, return true *)
        iApply ("HΦ" $! true). iSplitL.
        -- iExists (Datatypes.S n'). simpl. iExists v, next, S'. iFrame. iPureIntro. done.
        -- iPureIntro. rewrite bool_decide_eq_true_2; first done.
           set_solver.
      * (* val ≠ v, recurse *)
        wp_pures.
        wp_apply ("IH" $! next S' with "[Hrest]").
        { iFrame "#". iExists n'. iFrame. }
        iIntros (b) "[Hlist %Hb]". wp_pures.
        iApply ("HΦ" $! b). iSplitL.
        -- iDestruct "Hlist" as (n'') "Hlist".
           unfold is_list. iExists (Datatypes.S n''). simpl. iExists hd_val, next, S'.
           iFrame. iPureIntro. done.
        -- iPureIntro. subst b. f_equal.
           apply bool_decide_ext. set_solver.
Qed.

Lemma wp_ListNode__InsertBackRecursive (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "InsertBackRecursive" #v
  {{{ (head' : loc), RET #head'; is_list head' ({[v]} ∪ S) }}}.
Proof.
  iLöb as "IH" forall (head S).
  wp_start as "Hlist".
  iDestruct "Hlist" as (n) "Hlist".
  destruct n as [|n'].
  - (* Base case: head = null, S = ∅ *)
    iDestruct "Hlist" as "[%Hnull %Hempty]". subst.
    wp_auto.
    wp_alloc newNode as "Hnew".
    wp_auto.
    iApply "HΦ".
    iStructNamed "Hnew". simpl.
    unfold is_list. iExists (Datatypes.S 0%nat). simpl.
    iExists v, null, ∅.
    iFrame. iPureIntro. split; first set_solver.
    done.
  - (* Inductive case *)
    simpl.
    iDestruct "Hlist" as (hd_val next S') "(%Heq & Hval & Hnext & Hrest)". subst.
    wp_auto.
    wp_if_destruct.
    + iExFalso.
      iApply (is_list_aux_non_null n' ({[hd_val]} ∪ S')).
      simpl. iExists hd_val, next, S'. iFrame. iPureIntro. done.
    + wp_pures.
      wp_apply ("IH" $! next S' with "[Hrest]").
      { iFrame "#". iExists n'. iFrame. }
      iIntros (head'') "Hlist". wp_auto.
      iApply "HΦ".
      iDestruct "Hlist" as (n'') "Hlist".
      unfold is_list. iExists (Datatypes.S n''). simpl.
      iExists hd_val, head'', ({[v]} ∪ S').
      iFrame. iPureIntro. set_solver.
Qed.

Lemma wp_ListNode__DeleteAllRecursive (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "DeleteAllRecursive" #v
  {{{ (head' : loc), RET #head'; is_list head' (S ∖ {[v]}) }}}.
Proof.
  iLöb as "IH" forall (head S).
  wp_start as "Hlist".
  iDestruct "Hlist" as (n) "Hlist".
  destruct n as [|n'].
  - (* Base case: head = null, S = ∅ *)
    iDestruct "Hlist" as "[%Hnull %Hempty]". subst.
    wp_auto.
    iApply "HΦ".
    unfold is_list. iExists 0%nat. simpl. iPureIntro.
    split; first done. set_solver.
  - (* Inductive case *)
    simpl.
    iDestruct "Hlist" as (hd_val next S') "(%Heq & Hval & Hnext & Hrest)". subst.
    wp_auto.
    wp_if_destruct.
    + iExFalso.
      iApply (is_list_aux_non_null n' ({[hd_val]} ∪ S')).
      simpl. iExists hd_val, next, S'. iFrame. iPureIntro. done.
    + (* Recurse on head.Next *)
      wp_pures.
      wp_apply ("IH" $! next S' with "[Hrest]").
      { iFrame "#". iExists n'. iFrame. }
      iIntros (head'') "Hlist". wp_auto.
      (* head.Next updated to head''; now check head.Val == v *)
      wp_if_destruct.
      * (* hd_val = v: skip this node, return head.Next *)
        iApply "HΦ".
        replace (({[v]} ∪ S') ∖ {[v]}) with (S' ∖ {[v]}) by set_solver.
        done.
      * (* hd_val ≠ v: keep this node, return head *)
        wp_pures.
        iApply "HΦ".
        iDestruct "Hlist" as (n'') "Hlist".
        replace (({[hd_val]} ∪ S') ∖ {[v]}) with ({[hd_val]} ∪ (S' ∖ {[v]})) by set_solver.
        unfold is_list. iExists (Datatypes.S n''). simpl.
        iExists hd_val, head'', (S' ∖ {[v]}).
        iFrame. iPureIntro. done.
Qed.

Lemma wp_ListNode__CopyListRecursive (head : loc) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "CopyListRecursive" #()
  {{{ (head' : loc), RET #head'; is_list head S ∗ is_list head' S }}}.
Proof.
  iLöb as "IH" forall (head S).
  wp_start as "Hlist".
  iDestruct "Hlist" as (n) "Hlist".
  destruct n as [|n'].
  - (* Base case: head = null, S = ∅ *)
    iDestruct "Hlist" as "[%Hnull %Hempty]". subst.
    wp_auto.
    iApply "HΦ". iSplitL.
    + iExists 0%nat. simpl. iPureIntro. done.
    + iExists 0%nat. simpl. iPureIntro. done.
  - (* Inductive case *)
    simpl.
    iDestruct "Hlist" as (hd_val next S') "(%Heq & Hval & Hnext & Hrest)". subst.
    wp_auto.
    wp_if_destruct.
    + iExFalso.
      iApply (is_list_aux_non_null n' ({[hd_val]} ∪ S')).
      simpl. iExists hd_val, next, S'. iFrame. iPureIntro. done.
    + (* Recurse on head.Next *)
      wp_pures.
      wp_apply ("IH" $! next S' with "[Hrest]").
      { iFrame "#". iExists n'. iFrame. }
      iIntros (head'') "[Hrest Hcopy]".
      wp_pures. wp_alloc newNode as "Hnew".
      wp_auto.
      iApply "HΦ". iSplitL "Hval Hnext Hrest".
      * (* Original list *)
        iDestruct "Hrest" as (n'') "Hrest".
        unfold is_list. iExists (Datatypes.S n''). simpl.
        iExists hd_val, next, S'. iFrame. iPureIntro. done.
      * (* Copy *)
        iStructNamed "Hnew". simpl.
        iDestruct "Hcopy" as (n'') "Hcopy".
        unfold is_list. iExists (Datatypes.S n''). simpl.
        iExists hd_val, head'', S'. iFrame. iPureIntro. done.
Qed.

(* ===== List segment predicate and helpers for iterative proofs ===== *)

Fixpoint is_list_seg (n : nat) (from : loc) (S : gset w64) (to : loc) : iProp Σ :=
  match n with
  | O => ⌜from = to⌝ ∗ ⌜S = ∅⌝
  | Datatypes.S n' =>
    ∃ (v : w64) (next : loc) (S' : gset w64),
      ⌜S = {[v]} ∪ S'⌝ ∗
      from.[(heapexamples.ListNode.t), "Val"] ↦ v ∗
      from.[(heapexamples.ListNode.t), "Next"] ↦ next ∗
      is_list_seg n' next S' to
  end.

(* Append a list segment to a list *)
Lemma is_list_seg_append (n1 n2 : nat) (from mid : loc) (S1 S2 : gset w64) :
  is_list_seg n1 from S1 mid -∗ is_list_aux n2 mid S2 -∗
  is_list_aux (n1 + n2) from (S1 ∪ S2).
Proof. Admitted.

(* Extend a segment by one node at the end *)
Lemma is_list_seg_snoc (n : nat) (from mid : loc) (S_prefix : gset w64)
    (hd_val : w64) (next : loc) :
  is_list_seg n from S_prefix mid -∗
  mid.[(heapexamples.ListNode.t), "Val"] ↦ hd_val -∗
  mid.[(heapexamples.ListNode.t), "Next"] ↦ next -∗
  is_list_seg (Datatypes.S n) from (S_prefix ∪ {[hd_val]}) next.
Proof.
  iIntros "Hseg Hval Hnext".
  iInduction n as [|n'] "IH" forall (from S_prefix).
  - simpl. iDestruct "Hseg" as "[%Heq %Hempty]". subst.
    simpl. iExists hd_val, next, ∅. iFrame.
    iPureIntro. split; [set_solver | done].
  - simpl. iDestruct "Hseg" as (v' next' S'') "(%Heq & Hval' & Hnext' & Hseg')".
    simpl. iExists v', next', (S'' ∪ {[hd_val]}).
    iFrame "Hval' Hnext'".
    iSplitR "Hseg' Hval Hnext".
    + iPureIntro. subst. set_solver.
    + iApply ("IH" with "Hseg' Hval Hnext").
Qed.

(* Join segment with list *)
Lemma is_list_seg_to_list (from to : loc) (S1 S2 : gset w64) :
  (∃ n, is_list_seg n from S1 to) -∗ is_list to S2 -∗ is_list from (S1 ∪ S2).
Proof.
  iIntros "[%n1 Hseg] [%n2 Hlist]".
  iExists (n1 + n2)%nat.
  iApply (is_list_seg_append with "Hseg Hlist").
Qed.

(* ===== Iterative proofs ===== *)

Lemma wp_ListNode__Contains (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "Contains" #v
  {{{ (b : bool), RET #b; is_list head S ∗ ⌜b = bool_decide (v ∈ S)⌝ }}}.
Proof.
  wp_start as "Hlist".
  wp_auto.
  (* After wp_auto: "v" : v_ptr ↦ v, "cur" : cur_ptr ↦ head, "Hlist" : is_list head S *)
  iAssert (∃ (cur : loc) (n_prefix : nat) (S_prefix S_rest : gset w64),
    "cur" ∷ cur_ptr ↦ cur ∗
    "v" ∷ v_ptr ↦ v ∗
    "Hseg" ∷ is_list_seg n_prefix head S_prefix cur ∗
    "Hrest" ∷ is_list cur S_rest ∗
    "%HS" ∷ ⌜S = S_prefix ∪ S_rest⌝ ∗
    "%Hnotin" ∷ ⌜v ∉ S_prefix⌝
  )%I with "[cur v Hlist]" as "IH".
  { iExists head, 0%nat, ∅, S.
    iFrame "cur v Hlist".
    iSplitL.
    - simpl. iPureIntro. done.
    - iPureIntro. split; set_solver. }
  wp_for "IH".
  wp_if_destruct.
  - (* Loop exit: cur = null *)
    iDestruct "Hrest" as (n_rest) "Hrest".
    destruct n_rest as [|n_rest'].
    + (* n_rest = 0: S_rest = ∅ *)
      simpl. iDestruct "Hrest" as "[_ %Hempty]".
      iApply ("HΦ" $! false). iSplitL.
      * rewrite Hempty.
        iApply (is_list_seg_to_list with "[Hseg] []").
        { iExists n_prefix. iFrame. }
        { unfold is_list. iExists 0%nat. simpl. iPureIntro. done. }
      * iPureIntro. rewrite bool_decide_eq_false_2; first done.
        rewrite Hempty. set_solver.
    + (* n_rest > 0 but location is null: contradiction *)
      iExFalso. iApply (is_list_aux_non_null n_rest' S_rest).
      simpl. iDestruct "Hrest" as (hd_val next S'') "(%Heq & Hval & Hnext & Hrest')".
      iExists hd_val, next, S''. iFrame. iPureIntro. done.
  - (* Loop body: cur ≠ null *)
    iDestruct "Hrest" as (n_rest) "Hrest".
    destruct n_rest as [|n_rest'].
    + (* n_rest = 0: cur = null, but cur ≠ null — contradiction *)
      simpl. iDestruct "Hrest" as "[%Hnull _]". subst. done.
    + (* n_rest = S n_rest': unfold to access cur's fields *)
      simpl. iDestruct "Hrest" as (hd_val next S'') "(%Heq_rest & Hval & Hnext & Hrest')".
      wp_auto.
      wp_if_destruct.
      * (* hd_val = v: found it, return true *)
        wp_for_post.
        iApply ("HΦ" $! true). iSplitL.
        -- iApply (is_list_seg_to_list with "[Hseg] [Hval Hnext Hrest']").
           { iExists n_prefix. iFrame. }
           { unfold is_list. iExists (Datatypes.S n_rest'). simpl.
             iExists v, next, S''. iFrame. iPureIntro. done. }
        -- iPureIntro. rewrite bool_decide_eq_true_2; first done.
           set_solver.
      * (* hd_val ≠ v: continue to next iteration *)
        wp_for_post.
        iFrame "HΦ".
        iExists next, (Datatypes.S n_prefix), (S_prefix ∪ {[hd_val]}), S''.
        iFrame "cur v".
        iSplitL "Hseg Hval Hnext".
        -- iApply (is_list_seg_snoc with "Hseg Hval Hnext").
        -- iSplitL "Hrest'".
           ++ unfold is_list. iExists n_rest'. iFrame.
           ++ iPureIntro. subst. split; [set_solver | set_solver].
Qed.

Lemma wp_ListNode__InsertBack (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "InsertBack" #v
  {{{ (head' : loc), RET #head'; is_list head' ({[v]} ∪ S) }}}.
Proof.
  wp_start as "Hlist".
  wp_auto.
  wp_alloc newNode_loc as "Hnew".
  iStructNamed "Hnew". simpl.
  wp_auto.
  wp_if_destruct.
  - (* head = null: return newNode *)
    iDestruct "Hlist" as (n) "Hlist".
    destruct n as [|n'].
    + iDestruct "Hlist" as "[_ %Hempty]". subst.
      iApply "HΦ".
      unfold is_list. iExists (Datatypes.S 0%nat). simpl.
      iExists v, null, ∅.
      iFrame. iPureIntro. done.
    + iExFalso. iApply (is_list_aux_non_null n' S). iFrame.
  - (* head ≠ null: walk to the last node, append newNode *)
    iDestruct "Hlist" as (n0) "Hlist".
    destruct n0 as [|n0'].
    + simpl. iDestruct "Hlist" as "[%Hnull _]". subst. done.
    + simpl. iDestruct "Hlist" as (hd_val nxt S') "(%Heq & Hval & Hnxt & Hrest)".
      (* Loop invariant: expose cur's fields for condition (cur.Next != null) *)
      iAssert (∃ (cur : loc) (cur_val : w64) (cur_nxt : loc)
                 (n_prefix : nat) (S_prefix S_rest : gset w64),
        "cur"     ∷ cur_ptr ↦ cur ∗
        "Hcv"     ∷ cur.[(heapexamples.ListNode.t), "Val"] ↦ cur_val ∗
        "Hcn"     ∷ cur.[(heapexamples.ListNode.t), "Next"] ↦ cur_nxt ∗
        "Hseg"    ∷ is_list_seg n_prefix head S_prefix cur ∗
        "Hrest"   ∷ is_list cur_nxt S_rest ∗
        "Hnv"     ∷ newNode_loc.[(heapexamples.ListNode.t), "Val"] ↦ v ∗
        "Hnn"     ∷ newNode_loc.[(heapexamples.ListNode.t), "Next"] ↦ null ∗
        "newNode" ∷ newNode_ptr ↦ newNode_loc ∗
        "head"    ∷ head_ptr ↦ head ∗
        "%HS"     ∷ ⌜S = S_prefix ∪ {[cur_val]} ∪ S_rest⌝
      )%I with "[cur Hval Hnxt Val Next newNode head Hrest]" as "IH".
      { iExists head, hd_val, nxt, 0%nat, ∅, S'.
        iFrame "cur Hval Hnxt Val Next newNode head".
        (* Remaining: is_list_seg 0 head ∅ head ∗ is_list nxt S' ∗ ⌜S = ...⌝ *)
        iSplitR "Hrest".
        - (* is_list_seg 0 head ∅ head *)
          simpl. iPureIntro. done.
        - iSplitL "Hrest".
          + unfold is_list. iExists n0'. iFrame.
          + iPureIntro. rewrite Heq. set_solver. }
      wp_for "IH".
      wp_if_destruct.
      * (* Loop exit: cur_nxt = null *)
        iDestruct "Hrest" as (n_rest) "Hrest".
        destruct n_rest as [|n_rest'].
        -- simpl. iDestruct "Hrest" as "[_ %Hempty]".
           (* Goal: Φ (#head) — wp_for "IH" already processed the post-loop store+return *)
           iApply ("HΦ" $! head).
           assert (Hset : {[v]} ∪ ({[hd_val]} ∪ S') = (S_prefix ∪ {[cur_val]}) ∪ {[v]}).
           { set_solver. }
           rewrite Hset.
           iApply (is_list_seg_to_list head newNode_loc (S_prefix ∪ {[cur_val]}) {[v]}
             with "[Hseg Hcv Hcn] [Hnv Hnn]").
           ++ iExists (Datatypes.S n_prefix).
              iApply (is_list_seg_snoc with "Hseg Hcv Hcn").
           ++ unfold is_list. iExists (Datatypes.S 0%nat). simpl.
              iExists v, null, ∅. iFrame "Hnv Hnn". iPureIntro. set_solver.
        -- iExFalso. iApply (is_list_aux_non_null n_rest' S_rest).
           simpl. iDestruct "Hrest" as (rv rn rs) "(%Heq2 & Hrv & Hrn & Hrest')".
           iExists rv, rn, rs. iFrame. iPureIntro. done.
      * (* Loop body: cur_nxt ≠ null, advance cur *)
        iDestruct "Hrest" as (n_rest) "Hrest".
        destruct n_rest as [|n_rest'].
        -- simpl. iDestruct "Hrest" as "[%Hnull _]". subst. done.
        -- simpl. iDestruct "Hrest" as (next_val next_nxt S'') "(%Heq2 & Hnval & Hnnxt & Hrest')".
           wp_pures.
           wp_for_post.
           iFrame "HΦ".
           iExists cur_nxt, next_val, next_nxt, (Datatypes.S n_prefix), (S_prefix ∪ {[cur_val]}), S''.
           iFrame "cur Hnval Hnnxt Hnv Hnn newNode head".
           iSplitL "Hseg Hcv Hcn".
           ++ iApply (is_list_seg_snoc with "Hseg Hcv Hcn").
           ++ iSplitL "Hrest'". { unfold is_list. iExists n_rest'. iFrame. }
              iPureIntro. set_solver.
Qed.

Lemma wp_ListNode__CopyList (head : loc) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "CopyList" #()
  {{{ (head' : loc), RET #head'; is_list head S ∗ is_list head' S }}}.
Proof.
  wp_start as "Hlist".
  wp_auto.
  wp_if_destruct.
  - (* head = null: return null *)
    iDestruct "Hlist" as (n) "Hlist".
    destruct n as [|n'].
    + simpl. iDestruct "Hlist" as "[_ %Hempty]". subst.
      iApply "HΦ". iSplitL.
      * unfold is_list. iExists 0%nat. simpl. iPureIntro. done.
      * unfold is_list. iExists 0%nat. simpl. iPureIntro. done.
    + iExFalso. iApply (is_list_aux_non_null n' S). iFrame.
  - (* head ≠ null *)
    iDestruct "Hlist" as (n0) "Hlist".
    destruct n0 as [|n0'].
    + simpl. iDestruct "Hlist" as "[%Hnull _]". subst. done.
    + simpl. iDestruct "Hlist" as (hd_val nxt S') "(%Heq & Hval & Hnxt & Hrest)".
      (* wp_auto reads head.Val, then stops at GoAlloc for newHead *)
      wp_auto.
      wp_alloc newHead_loc as "HnewHead".
      iStructNamed "HnewHead". simpl.
      (* wp_auto processes: store newHead, cur := head.Next, tail := newHead *)
      wp_auto.
      (* Loop invariant:
         cur walks the original list, tail tracks end of new list.
         Original: is_list_seg from head to cur, is_list from cur onward.
         New: is_list_seg from newHead to tail, tail's fields exposed.
         The copied set matches the original prefix. *)
      iAssert (∃ (cur_loc tail_loc : loc) (tail_val : w64)
                 (n_orig n_new : nat)
                 (S_orig_prefix S_new_prefix S_rest : gset w64),
        "cur"     ∷ cur_ptr ↦ cur_loc ∗
        "tail"    ∷ tail_ptr ↦ tail_loc ∗
        "newHead" ∷ newHead_ptr ↦ newHead_loc ∗
        "Htv"     ∷ tail_loc.[(heapexamples.ListNode.t), "Val"] ↦ tail_val ∗
        "Htn"     ∷ tail_loc.[(heapexamples.ListNode.t), "Next"] ↦ null ∗
        "Horig"   ∷ is_list_seg n_orig head S_orig_prefix cur_loc ∗
        "Hrest"   ∷ is_list cur_loc S_rest ∗
        "Hnew"    ∷ is_list_seg n_new newHead_loc S_new_prefix tail_loc ∗
        "%HS"     ∷ ⌜S = S_orig_prefix ∪ S_rest⌝ ∗
        "%HSnew"  ∷ ⌜S_orig_prefix = S_new_prefix ∪ {[tail_val]}⌝
      )%I with "[cur tail newHead Hval Hnxt Hrest Val Next]" as "IH".
      { iExists nxt, newHead_loc, hd_val, 1%nat, 0%nat, {[hd_val]}, ∅, S'.
        iFrame "cur tail newHead Val Next".
        iSplitL "Hval Hnxt".
        - (* is_list_seg 1 head {[hd_val]} nxt *)
          simpl. iExists hd_val, nxt, ∅. iFrame. iPureIntro. split; [set_solver | done].
        - iSplitL "Hrest".
          + unfold is_list. iExists n0'. iFrame.
          + iSplitL.
            * simpl. iPureIntro. done.
            * iPureIntro. set_solver. }
      wp_for "IH".
      wp_if_destruct.
      * (* Loop exit: cur_loc = null *)
        iDestruct "Hrest" as (n_rest) "Hrest".
        destruct n_rest as [|n_rest'].
        -- simpl. iDestruct "Hrest" as "[_ %Hempty]".
           (* Post-loop: return newHead *)
           (* S was substituted to {[hd_val]} ∪ S' by %Heq.
              S_orig_prefix was substituted to S_new_prefix ∪ {[tail_val]} by %HSnew.
              HS : {[hd_val]} ∪ S' = (S_new_prefix ∪ {[tail_val]}) ∪ S_rest
              Hempty : S_rest = ∅ *)
           iApply ("HΦ" $! newHead_loc).
           (* Goal: is_list head ({[hd_val]} ∪ S') ∗ is_list newHead_loc ({[hd_val]} ∪ S') *)
           assert (Hset : {[hd_val]} ∪ S' = (S_new_prefix ∪ {[tail_val]}) ∪ ∅).
           { set_solver. }
           iSplitL "Horig".
           ++ (* Reconstruct original list *)
              rewrite Hset.
              iApply (is_list_seg_to_list head null (S_new_prefix ∪ {[tail_val]}) ∅
                with "[Horig] []").
              ** iExists n_orig. iFrame.
              ** unfold is_list. iExists 0%nat. simpl. iPureIntro. done.
           ++ (* Reconstruct new list *)
              assert (Hset2 : {[hd_val]} ∪ S' = S_new_prefix ∪ {[tail_val]}).
              { set_solver. }
              rewrite Hset2.
              iApply (is_list_seg_to_list newHead_loc tail_loc S_new_prefix {[tail_val]}
                with "[Hnew] [Htv Htn]").
              ** iExists n_new. iFrame.
              ** unfold is_list. iExists (Datatypes.S 0%nat). simpl.
                 iExists tail_val, null, ∅. iFrame "Htv Htn". iPureIntro. set_solver.
        -- iExFalso. iApply (is_list_aux_non_null n_rest' S_rest).
           simpl. iDestruct "Hrest" as (rv rn rs) "(%Heq2 & Hrv & Hrn & Hrest')".
           iExists rv, rn, rs. iFrame. iPureIntro. done.
      * (* Loop body: cur_loc ≠ null *)
        iDestruct "Hrest" as (n_rest) "Hrest".
        destruct n_rest as [|n_rest'].
        -- simpl. iDestruct "Hrest" as "[%Hnull _]". subst. done.
        -- simpl. iDestruct "Hrest" as (cur_val cur_nxt S'') "(%Heq2 & Hcv & Hcn & Hrest')".
           (* wp_auto reads cur.Val, stops at GoAlloc *)
           wp_auto.
           wp_alloc new_node_loc as "Hnewnode".
           iStructNamed "Hnewnode". simpl.
           (* Process: tail.Next = new_node, tail = tail.Next, cur = cur.Next *)
           wp_auto.
           wp_for_post.
           iFrame "HΦ".
           (* After substitutions by %Heq, %HSnew, %Heq2:
              S → {[hd_val]} ∪ S'
              S_orig_prefix → S_new_prefix ∪ {[tail_val]}
              S_rest → {[cur_val]} ∪ S'' (if subst'd by Heq2)
              Provide next-iteration witnesses with substituted forms *)
           iExists cur_nxt, new_node_loc, cur_val,
                   (Datatypes.S n_orig), (Datatypes.S n_new),
                   ((S_new_prefix ∪ {[tail_val]}) ∪ {[cur_val]}),
                   (S_new_prefix ∪ {[tail_val]}), S''.
           iFrame "cur tail newHead".
           (* new_node fields become the new tail's Val and Next *)
           iFrame "Val Next".
           iSplitL "Horig Hcv Hcn".
           ++ (* Extend original segment: is_list_seg_snoc *)
              iApply (is_list_seg_snoc with "Horig Hcv Hcn").
           ++ iSplitL "Hrest'".
              { unfold is_list. iExists n_rest'. iFrame. }
              iSplitL "Hnew Htv Htn".
              ** (* Extend new segment: is_list_seg_snoc *)
                 iApply (is_list_seg_snoc with "Hnew Htv Htn").
              ** iPureIntro. set_solver.
Qed.

Lemma wp_ListNode__DeleteAll (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "DeleteAll" #v
  {{{ (head' : loc), RET #head'; is_list head' (S ∖ {[v]}) }}}.
Proof.
  wp_start as "Hlist".
  wp_auto.
  (* LOOP 1: Remove matching nodes from front *)
  iAssert (∃ (head_loc : loc) (S_rem : gset w64),
    "head" ∷ head_ptr ↦ head_loc ∗
    "v"    ∷ v_ptr ↦ v ∗
    "Hlist" ∷ is_list head_loc S_rem ∗
    "%HS1" ∷ ⌜S ∖ {[v]} = S_rem ∖ {[v]}⌝
  )%I with "[head v Hlist]" as "IH1".
  { iExists head, S. iFrame. iPureIntro. done. }
  wp_for "IH1".
  iDestruct "Hlist" as (n_hd) "Hlist".
  destruct n_hd as [|n_hd'].
  - (* head_loc = null: condition → false, loop exit *)
    simpl. iDestruct "Hlist" as "[%Hnull %Hempty]". subst.
    wp_auto.
    (* condition evaluated to #false; resolve the nested decide *)
    rewrite decide_False; [|discriminate].
    rewrite decide_True; [|reflexivity].
    iPureIntro. (* probe *)
    (* Loop 2 condition: cur = null → false *)
    iAssert (∃ (cur_loc : loc),
      "cur" ∷ cur_ptr ↦ cur_loc ∗
      "head" ∷ head_ptr ↦ null ∗
      "v"   ∷ v_ptr ↦ v ∗
      "Hlist" ∷ is_list cur_loc (S_rem ∖ {[v]})
    )%I with "[cur head v]" as "IH2".
    { iExists null. iFrame.
      unfold is_list. iExists 0%nat. simpl. iPureIntro. set_solver. }
    wp_for "IH2".
    iDestruct "Hlist" as (n2) "Hlist2".
    destruct n2 as [|n2'].
    + simpl. iDestruct "Hlist2" as "[%Hn2 %He2]". subst.
      wp_auto. wp_if_destruct.
      iApply "HΦ".
      unfold is_list. iExists 0%nat. simpl. iPureIntro. set_solver.
    + simpl. iDestruct "Hlist2" as (cv cn cs) "(%Heq2 & Hcval & Hcnxt & Hcrest)".
      wp_auto. wp_if_destruct.
      * iExFalso. iApply (is_list_aux_non_null n2' (S_rem ∖ {[v]})).
        simpl. iDestruct "Hcrest" as "Hcrest".
        admit. (* null case shouldn't reach here *)
      * admit. (* shouldn't reach here either *)
  - (* head_loc ≠ null: expose fields, evaluate condition *)
    simpl. iDestruct "Hlist" as (hd_val nxt S') "(%Heq & Hval & Hnxt & Hrest)".
    wp_auto.
    wp_if_destruct.
    + (* hd_val = v: skip this node, advance head *)
      wp_pures.
      wp_for_post.
      iFrame "HΦ".
      iExists nxt, S'.
      iFrame "head v".
      iSplitL "Hrest".
      * unfold is_list. iFrame.
      * iPureIntro. set_solver.
    + (* hd_val ≠ v: exit loop 1, proceed to loop 2 *)
      (* Reconstruct is_list for head_loc, then set up loop 2 *)
      admit.
Admitted.

End proof.
