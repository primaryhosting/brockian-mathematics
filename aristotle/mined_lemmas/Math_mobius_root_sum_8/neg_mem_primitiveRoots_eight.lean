/-
# Mobius Root Sum 8
Category: Pure Mathematics
Target: Math.mobius_root_sum_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Math

/-- A primitive `8`-th root of unity satisfies `ζ ^ 4 = -1`. -/

lemma neg_mem_primitiveRoots_eight {z : ℂ} (hz : z ∈ primitiveRoots 8 ℂ) :
    -z ∈ primitiveRoots 8 ℂ := by
  rw [mem_primitiveRoots (by norm_num)] at hz ⊢
  have h5 : IsPrimitiveRoot (z ^ 5) 8 := hz.pow_of_coprime 5 (by norm_num [Nat.Coprime])
  have : z ^ 5 = -z := by
    have h4 := pow_four_eq_neg_one_of_isPrimitiveRoot_eight hz
    calc z ^ 5 = z ^ 4 * z := by ring
    _ = -z := by rw [h4]; ring
  rwa [this] at h5

/-- The sum of the primitive `8`-th roots of unity in `ℂ` equals `μ 8` (which is `0`).

The primitive `8`-th roots of unity are closed under negation and none of them is zero,
so they pair off and the sum vanishes; and `μ 8 = 0` since `8 = 2 ^ 3` is not squarefree. -/
