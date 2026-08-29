/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/

lemma dvd_qpoly_comp : (X ^ 13 - 1 : ℂ[X]) ∣ qpoly.comp (X + X ^ 12) := by
  rw [qpoly_comp_eq, Polynomial.X_pow_sub_one_eq_prod (by norm_num) zeta_primitive]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun w hw => ?_
  have hw1 : w ^ 13 = 1 := (Polynomial.mem_nthRootsFinset (by norm_num) _).1 hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw1
    simp at hw1
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  have h12 : w ^ 12 = w⁻¹ := by
    field_simp
    linear_combination hw1
  simp [h12]

