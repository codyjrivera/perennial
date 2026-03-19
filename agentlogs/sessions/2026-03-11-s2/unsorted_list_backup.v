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

(* Framework gap: struct_field_ref is abstract, so there is no general lemma
   deriving l ≠ null from a struct field pointsto at l. However, in the
   concrete Go semantics, the first field of any struct is at offset 0, so
   struct_field_ref _ "Val" l = l, and heap_pointsto_non_null gives l ≠ null.
   We state this as a helper until the framework exposes it. *)
Lemma is_list_aux_null_inv n S :
  is_list_aux (Datatypes.S n) null S -∗ False.
Proof. Admitted.

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

Lemma wp_ListNode__ContainsRecursive (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "ContainsRecursive" #v
  {{{ (b : bool), RET #b; is_list head S ∗ ⌜b = bool_decide (v ∈ S)⌝ }}}.
Proof.
  wp_start as "Hlist".
  iLöb as "IH" forall (head S) "Hlist HΦ".
  iDestruct "Hlist" as (n) "Hlist".
  destruct n as [|n].
  - (* Empty list: head = null *)
    simpl. iDestruct "Hlist" as "[-> ->]".
    wp_auto.
    iApply "HΦ". iSplit.
    + iExists 0%nat. simpl. auto.
    + iPureIntro. symmetry. apply bool_decide_eq_false_2. set_solver.
  - (* Non-empty list *)
    simpl. iDestruct "Hlist" as (val next S') "(%Heq & Hval & Hnext & Hrest)".
    subst S.
    wp_auto.
    wp_if_destruct.
    + (* head == null — impossible: non-empty list at null *)
      iExFalso.
      iApply (is_list_aux_null_inv n ({[val]} ∪ S')).
      simpl. iExists val, next, S'. iFrame. done.
    + (* head ≠ null *)
      wp_pures.
      wp_if_destruct.
      * (* head.Val == v *)
        iApply "HΦ". iSplit.
        { iExists (Datatypes.S n). simpl. iExists v, next, S'. iFrame. iPureIntro. done. }
        { iPureIntro. symmetry. apply bool_decide_eq_true_2. set_solver. }
      * (* head.Val ≠ v, recursive call *)
        iAssert (is_list next S') with "[Hrest]" as "Hrest".
        { iExists n. iFrame. }
        wp_bind (next @! (go.PointerType heapexamples.ListNode) @! "ContainsRecursive" #v)%E.
        iAssert (is_list next S') with "[Hrest]" as "Hrest".
        { iExists n. iFrame. }
        wp_apply ("IH" with "[$Hrest]").
        iIntros (b) "[Hrest %Hb]".
        iApply "HΦ". iSplit.
        { iDestruct "Hrest" as (m) "Hrest".
          iExists (Datatypes.S m). simpl. iExists val, next, S'. iFrame. iPureIntro. done. }
        { iPureIntro. subst b.
          destruct (bool_decide_reflect (v ∈ S')) as [Hin|Hnotin];
          destruct (bool_decide_reflect (v ∈ {[val]} ∪ S')) as [Hin'|Hnotin'].
          -- done.
          -- exfalso. apply Hnotin'. set_solver.
          -- exfalso. apply Hnotin. set_solver.
          -- done. }
Qed.

End proof.
