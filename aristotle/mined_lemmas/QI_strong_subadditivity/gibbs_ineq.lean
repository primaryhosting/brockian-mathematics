import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Real
open scoped ComplexOrder

namespace QI

/-! ## Von Neumann entropy and reduced density matrices -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a matrix, computed as the sum of
`negMulLog` over the eigenvalues.  (Defined to be `0` on non-Hermitian matrices.) -/

theorem gibbs_ineq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    u * (Real.log v - Real.log u) ≤ v - u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div (ne_of_gt hv) (ne_of_gt hu)] at h
  calc u * (Real.log v - Real.log u) ≤ u * (v / u - 1) := mul_le_mul_of_nonneg_left h hu.le
    _ = v - u := by field_simp

omit [DecidableEq A] [DecidableEq B] [DecidableEq C] in
/-- Strong subadditivity for the Shannon entropy of a nonnegative weight function on a
product of three finite sets, with the marginals given as explicit data. -/
