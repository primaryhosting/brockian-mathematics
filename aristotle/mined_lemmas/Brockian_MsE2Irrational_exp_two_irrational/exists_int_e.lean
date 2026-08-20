import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma exists_int_e (n : ℕ) :
    ∃ A : ℤ, (A : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), (1 : ℝ) ^ i / (i ! : ℝ) := by
  have key : (n ! : ℝ) * ∑ i ∈ range (n + 1), (1 : ℝ) ^ i / (i ! : ℝ)
           = ∑ i ∈ range (n + 1), (n ! : ℝ) / (i ! : ℝ) := by
    simp [Finset.mul_sum, div_eq_mul_inv, mul_comm]
  obtain ⟨A, hA⟩ := exists_int_sum n (fun _ => 1)
  simp at hA
  exact ⟨A, hA.trans key.symm⟩

/-- `n ! * (partial sum of the series for `e⁻¹`)` is an integer. -/
