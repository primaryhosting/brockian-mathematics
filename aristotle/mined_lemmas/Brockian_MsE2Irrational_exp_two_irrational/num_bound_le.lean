import Mathlib
namespace Brockian.MsE2Irrational

open Finset Nat

/-- `n ! / k !` computed in `ℕ` agrees with the real quotient when `k ≤ n`. -/

private lemma num_bound_le (n : ℕ) :
    1 / ((n : ℝ) + 1) + 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))
        + ((n : ℝ) + 4) / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 3))
      ≤ 2 / ((n : ℝ) + 1) := by
  field_simp
  ring_nf
  nlinarith [sq_nonneg (n : ℝ)]

