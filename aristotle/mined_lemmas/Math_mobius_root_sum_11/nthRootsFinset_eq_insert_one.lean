/-
# Mobius Root Sum 11
Category: Pure Mathematics
Target: Math.mobius_root_sum_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 11

The sum of the primitive 11-th roots of unity in `ℂ` equals `μ(11)`.
-/

open Finset Polynomial

namespace Math

/-- The 11-th roots of unity in `ℂ` are exactly the powers `ζ ^ i`, `i < 11`, of a primitive
11-th root of unity `ζ`. -/

lemma nthRootsFinset_eq_insert_one :
    nthRootsFinset 11 (1 : ℂ) = insert 1 (primitiveRoots 11 ℂ) := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
  have hdiv : Nat.divisors 11 = {1, 11} := by decide
  rw [hdiv]
  simp [Finset.biUnion_insert, IsPrimitiveRoot.primitiveRoots_one]

/-- `1` is not a primitive 11-th root of unity. -/
