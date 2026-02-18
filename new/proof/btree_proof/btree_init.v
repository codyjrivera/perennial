From New.generatedproof Require Import btree.
From New.proof Require Import proof_prelude.
From New.proof Require Import fmt strings.
From New.proof.sort_proof Require Import sort_init.
From New.proof Require Import internal.race sync.atomic.
From New.proof Require Import errors.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit io := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf io := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit btree := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf btree := build_get_is_pkg_init_wf.

End proof.
