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

theorem poly_comp_bound (n k c : ℕ) : ((n + 2) ^ k + 2) ^ c ≤ (n + 2) ^ ((k + 2) * c) := by
  have h1 : 1 ≤ (n + 2) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (n + 2) ^ k + 2 ≤ (n + 2) ^ (k + 2) := by
    have : (n + 2) ^ (k + 2) = (n + 2) ^ k * ((n + 2) * (n + 2)) := by ring
    have h4 : 4 * (n + 2) ^ k ≤ (n + 2) ^ k * ((n + 2) * (n + 2)) := by
      have : 4 ≤ (n + 2) * (n + 2) := by nlinarith
      calc 4 * (n + 2) ^ k ≤ ((n + 2) * (n + 2)) * (n + 2) ^ k := Nat.mul_le_mul_right _ this
        _ = (n + 2) ^ k * ((n + 2) * (n + 2)) := by ring
    omega
  calc ((n + 2) ^ k + 2) ^ c ≤ ((n + 2) ^ (k + 2)) ^ c := Nat.pow_le_pow_left h2 c
    _ = (n + 2) ^ ((k + 2) * c) := by rw [← pow_mul]

/-- Constant-gap PCPs transfer along polynomial-time many-one reductions. -/
