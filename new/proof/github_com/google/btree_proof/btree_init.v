From New.generatedproof.github_com.google Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof Require Import fmt strings.
From New.proof.sort_proof Require Import sort_init.
From New.proof Require Import internal.race sync.atomic.
From New.proof Require Import errors.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : btree.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) btree := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) btree := build_get_is_pkg_init_wf.
End proof.
