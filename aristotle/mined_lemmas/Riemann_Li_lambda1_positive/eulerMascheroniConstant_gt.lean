import Mathlib
/-!
# Lambda 1 Positive
Category: Riemann Program
Target: Riemann.Li.lambda1_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Li

/-- **Positivity of Li's first coefficient.**

Li's first coefficient is `λ₁ = 1 + γ/2 - (1/2) · log (4π)`, where `γ` is the
Euler–Mascheroni constant.  Using the numerical bounds `0.577 ≤ γ` and
`log (4π) ≤ 2.532`, positivity of `λ₁` follows from the arithmetic statement
below: for all reals `g, L` with `0.577 ≤ g` and `L ≤ 2.532`, we have
`0 < 1 + g/2 - L/2`.

(Li's criterion: the Riemann Hypothesis holds iff `λₙ ≥ 0` for all `n ≥ 1`.) -/

theorem eulerMascheroniConstant_gt : (0.5615 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 31
  have hval : Real.eulerMascheroniSeq 31
      = (290774257297357 / 72201776446800 : ℝ) - Real.log 32 := by
    rw [Real.eulerMascheroniSeq]
    norm_num [harmonic, Finset.sum_range_succ]
  have hlog : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [hval, hlog] at h
  nlinarith [h, h2]

/-- A verified upper bound for `log (4π)`. -/
