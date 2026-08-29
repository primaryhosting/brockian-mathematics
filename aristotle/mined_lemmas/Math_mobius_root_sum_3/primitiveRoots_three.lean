/-
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 3
Category: Pure Mathematics
Target: Math.mobius_root_sum_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- A fixed primitive cube root of unity in `ℂ`. -/

lemma primitiveRoots_three : primitiveRoots 3 ℂ = {zeta3, zeta3 ^ 2} := by
  have hz := isPrimitiveRoot_zeta3
  have hz2 : IsPrimitiveRoot (zeta3 ^ 2) 3 := hz.pow_of_coprime 2 (by decide)
  have hsub : ({zeta3, zeta3 ^ 2} : Finset ℂ) ⊆ primitiveRoots 3 ℂ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_primitiveRoots (by norm_num)).2 hz
    · exact (mem_primitiveRoots (by norm_num)).2 hz2
  have hcard : (primitiveRoots 3 ℂ).card = 2 := by
    rw [hz.card_primitiveRoots]
    decide
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Finset.card_insert_of_notMem (by simpa using zeta3_ne_sq), Finset.card_singleton]

/-- The sum of the primitive cube roots of unity equals `μ(3) = -1`. -/
