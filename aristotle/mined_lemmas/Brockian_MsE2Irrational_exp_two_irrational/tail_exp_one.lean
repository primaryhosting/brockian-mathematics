import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma tail_exp_one (n : ℕ) :
    ∃ A : ℤ, 0 < (n ! : ℝ) * Real.exp 1 - A ∧ (n ! : ℝ) * Real.exp 1 - A ≤ 2 / (n + 1) := by
  obtain ⟨A, hA⟩ := exists_int_e n
  use A
  have hx : |(1 : ℝ)| ≤ 1 := by norm_num
  have hbound := tail_key 1 hx n A hA
  -- For x = 1: 1^(n+1) = 1, 1^(n+2) = 1, so main terms = 1/(n+1) + 1/((n+1)(n+2))
  simp only [one_pow] at hbound
  have hnum_lt := num_bound_lt n
  have hnum_le := num_bound_le n
  have habs := abs_le.mp hbound
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- For `n` even, `n ! * e⁻¹` is strictly below an integer, by at most `2/(n+1)`. -/
