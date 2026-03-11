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
  wp_alloc head' as "Hnew".
  wp_auto.
  iStructNamed "Hnew".
  iApply "HΦ".
  unfold is_list.
  iDestruct "Hlist" as (n) "Hlist".
  iExists (Datatypes.S n).
  simpl.
  iExists v, head, S.
  iFrame.
  iPureIntro.
  set_solver.
Qed.

Lemma wp_ListNode__ContainsRecursive_aux (n : nat) (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list_aux n head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "ContainsRecursive" #v
  {{{ (b : bool), RET #b; is_list_aux n head S ∗ ⌜b = bool_decide (v ∈ S)⌝ }}}.
Proof.
  revert head S.
  induction n as [|n' IHn'].
  - (* Base case *)
    iIntros (head' S') "!# [#Hinit Haux] HΦ".
    simpl.
    iDestruct "Haux" as "[%Hnull %Hempty]".
    subst.
    wp_start as "_".
    wp_auto.
    iApply ("HΦ" $! false).
    iSplit.
    + simpl. iSplit; iPureIntro; done.
    + iPureIntro. symmetry. apply bool_decide_eq_false. set_solver.
  - (* Inductive case *)
    iIntros (head' S') "!# [#Hinit Haux] HΦ".
    simpl.
    iDestruct "Haux" as (val next S'') "[%Hunion [HVal [HNext Htail]]]".
    subst.
    wp_start as "_".
    wp_auto.
    wp_if_destruct.
    + (* val ≠ v *)
      wp_auto.
      wp_apply (IHn' with "[$Hinit $Htail]").
      iIntros (b) "[Htail %Hb]".
      wp_auto.
      iApply "HΦ".
      iSplit.
      * simpl. iExists val, next, S''. iFrame. iPureIntro. done.
      * iPureIntro. subst b. f_equal.
        apply propext. split; intros Hin.
        -- apply elem_of_union in Hin as [Hin|Hin]; first by apply elem_of_singleton_1 in Hin; exfalso; apply Heqb; word.
           exact Hin.
        -- apply elem_of_union_r. exact Hin.
    + (* val = v *)
      wp_auto.
      iApply ("HΦ" $! true). iSplit.
      * simpl. iExists val, next, S''. iFrame. iPureIntro. done.
      * iPureIntro. symmetry. apply bool_decide_eq_true. set_solver.
Admitted.

Lemma wp_ListNode__ContainsRecursive (head : loc) (v : w64) (S : gset w64) :
  {{{ is_pkg_init heapexamples ∗ is_list head S }}}
    head @! (go.PointerType heapexamples.ListNode) @! "ContainsRecursive" #v
  {{{ (b : bool), RET #b; is_list head S ∗ ⌜b = bool_decide (v ∈ S)⌝ }}}.
Proof.
  iIntros (Φ) "[#Hinit Hlist] HΦ".
  iDestruct "Hlist" as (n) "Haux".
  wp_apply (wp_ListNode__ContainsRecursive_aux with "[$Hinit $Haux]").
  iIntros (b) "[Haux %Hb]".
  iApply "HΦ". iSplit; last by iPureIntro.
  iExists n. iFrame.
Admitted.

End proof.
