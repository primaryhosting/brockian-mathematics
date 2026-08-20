import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma exists_int_sum (n : ℕ) (c : ℕ → ℤ) :
    ∃ A : ℤ, (A : ℝ) = ∑ k ∈ range (n + 1), (c k : ℝ) * ((n ! : ℝ) / (k ! : ℝ)) := by
  use ∑ k ∈ range (n + 1), c k * (n ! / k !)
  simp only [Int.cast_sum]
  rw [Finset.sum_congr rfl]
  intro k hk
  rw [Int.cast_mul]
  have hkn : k ≤ n := by linarith [mem_range.mp hk]
  congr 1
  exact fact_div_cast n k hkn

