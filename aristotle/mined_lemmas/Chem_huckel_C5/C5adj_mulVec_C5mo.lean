import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` on vertices `0,1,2,3,4`:
vertices `i` and `j` are adjacent iff `j ≡ i + 1` or `i ≡ j + 1` modulo `5`. -/

theorem C5adj_mulVec_C5mo (k : ℕ) :
    C5adj *ᵥ C5mo k = ((2 * Real.cos (2 * π * k / 5) : ℝ) : ℂ) • C5mo k := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, Complex.exp (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I) = w := ⟨_, rfl⟩
  have hmo : ∀ j : Fin 5, C5mo k j = w ^ (j : ℕ) := fun j => by rw [C5mo_apply, hw]
  have hw5 : w ^ 5 = 1 := by
    rw [← hw, ← Complex.exp_nat_mul,
      show ((5 : ℕ) : ℂ) * (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)
        = (k : ℤ) * (2 * (π : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hcos : ((2 * Real.cos (2 * π * k / 5) : ℝ) : ℂ) = w + w ^ 4 := by
    have h1 : ((Real.cos (2 * π * k / 5) : ℝ) : ℂ)
        = (Complex.exp (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)
          + Complex.exp (-(((2 * π * k / 5 : ℝ) : ℂ) * Complex.I))) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos]
      ring_nf
    have h2 : Complex.exp (-(((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)) = w ^ 4 := by
      rw [Complex.exp_neg, hw]
      have hwne : w ≠ 0 := by rw [← hw]; exact Complex.exp_ne_zero _
      field_simp
      linear_combination -hw5
    have h3 : ((2 * Real.cos (2 * π * k / 5) : ℝ) : ℂ)
        = 2 * ((Real.cos (2 * π * k / 5) : ℝ) : ℂ) := by push_cast; ring
    rw [h3, h1, h2, hw]
    ring
  funext i
  rw [Pi.smul_apply, smul_eq_mul, hcos]
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, C5adj,
      Matrix.of_apply, hmo, Fin.isValue] <;>
    norm_num <;>
    first
      | linear_combination -hw5
      | linear_combination (-w) * hw5
      | linear_combination (-w ^ 2) * hw5
      | linear_combination (-(1 + w ^ 3)) * hw5

end Chem

#print axioms Chem.huckel_C5
#print axioms Chem.C5adj_mulVec_C5mo

