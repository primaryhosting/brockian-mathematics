/-
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalize the Kirby–Paris hydra game and prove that **every** play terminates,
no matter which head Hercules chops and no matter how many copies the hydra grows
at each stage (so, in particular, for every strategy).

A hydra is a finite rooted tree, encoded as `Hydra.node : List Hydra → Hydra`.
A *head* is a leaf.  In one move Hercules chops off a head; if the head has a
grandparent, the grandparent grows `n` extra copies of the subtree hanging at the
head's parent (with the head already removed).  The number `n` may be arbitrary
and may change from move to move.

The proof is the classical one: we attach to a hydra the ordinal
`o(node [h₁,…,h_k]) = ω ^ o(h₁) ♯ ⋯ ♯ ω ^ o(h_k) < ε₀`
(`♯` is the natural / Hessenberg sum) and check that every move strictly decreases
it; well-foundedness of the ordinals then finishes the argument.

The ordinal-arithmetic input that is not in Mathlib is that `ω ^ d` is closed under
natural sums; this is proved from scratch in the first section
(`Frontier.nadd_lt_opow_omega0`).

By the Kirby–Paris theorem this termination statement is not provable in Peano
arithmetic; the proof below is of course carried out in the ambient set theory of
Lean/Mathlib, where transfinite induction below ε₀ is available.
-/

open Ordinal NaturalOps

namespace Frontier

/-! ## Part 1: `ω ^ d` is closed under natural addition -/

/-- The key estimate: natural addition of two ordinals below `W * ω` is bounded by
the "Cantor-like" expression built from their quotients and remainders modulo `W`,
provided `W` itself is closed under natural addition. -/

theorem ord_lt_of_deepStep {n : ℕ} {h h' : Hydra} (hs : DeepStep n h h') : ord h' < ord h := by
  induction hs with
  | copy pre post hc =>
      rename_i c c'
      have hcc : ord c' < ord c := ord_lt_of_chopHead hc
      have hrep : ordList (List.replicate (n + 1) c') < ω ^ ord c := by
        refine ordList_lt_opow _ _ ?_
        intro x hx
        rw [List.eq_of_mem_replicate hx]
        exact hcc
      simp only [ord_node, ordList_append, ordList_cons, Ordinal.nadd_assoc]
      exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right hrep _) _
  | deep pre post _ ih =>
      simp only [ord_node, ordList_append, ordList_cons]
      refine Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right ?_ _) _
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 ih

/-- Every move of the hydra game strictly decreases the ordinal of the hydra. -/
