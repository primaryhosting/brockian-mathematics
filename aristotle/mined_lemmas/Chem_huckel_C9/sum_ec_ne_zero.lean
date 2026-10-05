import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma sum_ec_ne_zero {c : ZMod 9} (hc : c ≠ 0) : ∑ x : ZMod 9, ec (c * x) = 0 := by
  have key : ec c * (∑ x : ZMod 9, ec (c * x)) = ∑ x : ZMod 9, ec (c * x) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (1 : ZMod 9)) (fun x => ec (c * x))]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_addRight, mul_add, mul_one, ec_add, mul_comm]
  have h2 : (ec c - 1) * (∑ x : ZMod 9, ec (c * x)) = 0 := by linear_combination key
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) (ec_ne_one hc)
  · exact h

