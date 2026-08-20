/-
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! ## Words, languages, proofs -/

/-- A binary word. -/
abbrev Word := List Bool

/-- A language: a set of binary words. -/
abbrev Lang := Word → Prop

/-- A PCP proof (proof oracle): an infinite binary string. -/
abbrev Assignment := ℕ → Bool

/-! ## Local tests (constraints)

A non-adaptive PCP verifier, on a fixed input `x` and a fixed random string, reads a fixed
tuple of positions of the proof oracle and applies a predicate to the bits it read.  Such a
single action is exactly a *constraint*.
-/

/-- A single local test: a list of queried proof positions together with a predicate on the
answers. -/
structure Constraint where
  /-- The positions of the proof oracle that are queried. -/
  vars : List ℕ
  /-- The acceptance predicate applied to the answers, in the order of `vars`. -/
  pred : List Bool → Bool

/-- The number of queries made by a test. -/

def PCPclass (M : EffModel) : Set Lang :=
  {L | ∃ (V : Word → TestSystem) (q c : ℕ), M.Sys V ∧
        (∀ x : Word, ∀ t ∈ (V x).tests, t.arity ≤ q) ∧
        (∀ x : Word, (V x).tests.length ≤ (x.length + 2) ^ c) ∧
        (∀ x : Word, ∀ t ∈ (V x).tests, ∀ i ∈ t.vars, i < (x.length + 2) ^ c) ∧
        (∀ x : Word, L x → ∃ a : Assignment, acceptProb (V x) a = 1) ∧
        (∀ x : Word, ¬ L x → ∀ a : Assignment, acceptProb (V x) a ≤ 1 / 2)}

/-! ## The combinatorial core of the PCP theorem

The deep content of the PCP theorem (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy; Dinur's
proof) is the existence of *constant-gap* probabilistically checkable proofs for NP: every NP
language admits an efficient reduction to a system of `O(1)`-query local tests such that YES
instances are perfectly satisfiable while for NO instances every proof fails a constant
fraction of the tests.  This is stated here as a hypothesis; it is not proved in this
development.  What *is* proved below is that this hypothesis is equivalent to the equality
`NP = PCP(log n, 1)`: the soundness amplification from a constant gap to `1/2`, and the
converse inclusion `PCP(log n, 1) ⊆ NP`, are established unconditionally.  It is further
shown (`pcp_theorem_of_gap_npHard`) that it suffices to assume the constant gap for a single
NP-hard language, since constant-gap PCPs transfer along polynomial-time reductions.
-/

/-- `GapVerifier M L`: the language `L` has an efficient `O(1)`-query PCP verifier with
perfect completeness and a *constant* soundness gap `eps > 0`. -/
