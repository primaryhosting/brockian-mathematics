/-
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede any module docstring, so the header above is
repeated as a module docstring below the import.)
-/

import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Real Finset

namespace QI

/-! ## Von Neumann entropy -/

open scoped Classical in
/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, computed as
`∑ i, negMulLog (λ i)` over the eigenvalues of `ρ`. (Junk value `0` for non-Hermitian input.) -/

theorem q_sum_le_one (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∑ x : A × B × C, margAB p (x.1, x.2.1) * margBC p (x.2.1, x.2.2) / margB p x.2.1 ≤ 1 := by
  have step : ∑ x : A × B × C, margAB p (x.1, x.2.1) * margBC p (x.2.1, x.2.2) / margB p x.2.1
      = ∑ b, (∑ a, margAB p (a, b)) * (∑ c, margBC p (b, c)) / margB p b := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [step]
  calc ∑ b, (∑ a, margAB p (a, b)) * (∑ c, margBC p (b, c)) / margB p b
      ≤ ∑ b, margB p b := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [sum_margAB_eq_margB, sum_margBC_eq_margB]
        rcases eq_or_lt_of_le (margB_nonneg p hp0 b) with h | h
        · simp [← h]
        · rw [mul_div_assoc, div_self (ne_of_gt h), mul_one]
    _ = 1 := sum_margB_eq p hp1

