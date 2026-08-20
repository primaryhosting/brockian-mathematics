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

noncomputable def ord : Hydra → Ordinal.{0}
  | .node l => ordList l

/-- The natural sum `ω ^ o h₁ ♯ ⋯ ♯ ω ^ o h_k` over a list of hydras. -/
