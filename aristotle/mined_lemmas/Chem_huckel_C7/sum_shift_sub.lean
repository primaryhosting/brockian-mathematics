import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma sum_shift_sub (v : Fin 7 → ℂ) (k : Fin 7) :
    ∑ i : Fin 7, ee (-(i * k)) * v (i - 1)
      = ee (-k) * ∑ i : Fin 7, ee (-(i * k)) * v i := by
  rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin 7)) (fun i => ee (-(i * k)) * v (i - 1))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have h : -((i + 1) * k) = -k + -(i * k) := by decide +revert
  rw [h, ee_add, mul_assoc]

