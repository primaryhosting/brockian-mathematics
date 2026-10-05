import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

lemma proj2_add_eq_one {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) (hQ : IsProj Q)
    (hPQ : P * Q = 0) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P + Q = 1 := by
  have hQP : Q * P = 0 := by
    have h : (P * Q)ᴴ = (0 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [hPQ]
    rwa [Matrix.conjTranspose_mul, hP.1, hQ.1, Matrix.conjTranspose_zero] at h
  have hR : IsProj (P + Q) := by
    refine ⟨Matrix.IsHermitian.add hP.1 hQ.1, ?_⟩
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hPQ, hQP, hP.2, hQ.2]
    abel
  have htr : (P + Q).trace = P.trace + Q.trace := Matrix.trace_add P Q
  have hreal : hR.1.eigenvalues 0 + hR.1.eigenvalues 1
      = (hP.1.eigenvalues 0 + hP.1.eigenvalues 1) + (hQ.1.eigenvalues 0 + hQ.1.eigenvalues 1) := by
    have hc : ((hR.1.eigenvalues 0 + hR.1.eigenvalues 1 : ℝ) : ℂ)
        = (((hP.1.eigenvalues 0 + hP.1.eigenvalues 1) +
            (hQ.1.eigenvalues 0 + hQ.1.eigenvalues 1) : ℝ) : ℂ) := by
      rw [← trace2_eq_sum_eigenvalues hR.1, htr, trace2_eq_sum_eigenvalues hP.1,
        trace2_eq_sum_eigenvalues hQ.1]
      push_cast
      ring
    exact_mod_cast hc
  obtain ⟨jP, hjP⟩ := proj_exists_eigenvalue_one hP hP0
  obtain ⟨jQ, hjQ⟩ := proj_exists_eigenvalue_one hQ hQ0
  have hPge : 1 ≤ hP.1.eigenvalues 0 + hP.1.eigenvalues 1 := by
    rcases fin_two_cases jP with rfl | rfl
    · linarith [proj_eigenvalues_nonneg hP 1, hjP]
    · linarith [proj_eigenvalues_nonneg hP 0, hjP]
  have hQge : 1 ≤ hQ.1.eigenvalues 0 + hQ.1.eigenvalues 1 := by
    rcases fin_two_cases jQ with rfl | rfl
    · linarith [proj_eigenvalues_nonneg hQ 1, hjQ]
    · linarith [proj_eigenvalues_nonneg hQ 0, hjQ]
  have h0 := proj_eigenvalues_eq_zero_or_one hR 0
  have h1 := proj_eigenvalues_eq_zero_or_one hR 1
  refine proj_eq_one_of_eigenvalues_one hR fun j => ?_
  have hboth : hR.1.eigenvalues 0 = 1 ∧ hR.1.eigenvalues 1 = 1 := by
    rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rw [e0, e1] at hreal <;>
      refine ⟨?_, ?_⟩ <;> first | assumption | linarith
  rcases fin_two_cases j with rfl | rfl
  · exact hboth.1
  · exact hboth.2

/-! ## The counterexample -/

/-- Tie-breaking rule on nonzero complex numbers: exactly one of `z`, `-z` gets the value `1`. -/
