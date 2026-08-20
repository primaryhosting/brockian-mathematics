import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma exists_int_einv (n : ℕ) :
    ∃ B : ℤ, (B : ℝ) = (n ! : ℝ) * ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i / (i ! : ℝ) := by
  obtain ⟨B, hB⟩ := exists_int_sum n (fun i => (-1) ^ i)
  refine ⟨B, ?_⟩
  simp only [hB]
  simp [Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_assoc]

