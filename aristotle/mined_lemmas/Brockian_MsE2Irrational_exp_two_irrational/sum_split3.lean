import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma sum_split3 (x : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 3), x ^ i / (i ! : ℝ)
      = (∑ i ∈ range (n + 1), x ^ i / (i ! : ℝ)) + x ^ (n + 1) / ((n + 1)! : ℝ)
          + x ^ (n + 2) / ((n + 2)! : ℝ) := by
  simp only [← Finset.sum_range_succ]

