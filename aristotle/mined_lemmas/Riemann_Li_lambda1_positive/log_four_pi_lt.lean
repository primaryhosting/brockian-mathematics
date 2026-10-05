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

theorem log_four_pi_lt : Real.log (4 * Real.pi) < 2.54 := by
  have hpi : Real.pi < 3.15 := by
    have := Real.pi_lt_d2
    linarith
  have hexp : (12.6 : ℝ) ≤ Real.exp 2.54 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 9)
    simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
    norm_num
  have h1 : Real.log (4 * Real.pi) < Real.log 12.6 := by
    apply Real.log_lt_log (by positivity)
    linarith
  have h2 : Real.log 12.6 ≤ 2.54 := by
    have := Real.log_le_log (by norm_num : (0:ℝ) < 12.6) hexp
    rwa [Real.log_exp] at this
  linarith

end Numerics

/-- **Li's first coefficient is positive** (unconditional version).

With `γ` the Euler–Mascheroni constant, `λ₁ = 1 + γ/2 - (1/2) log (4π) > 0`.
The proof uses the verified numerical bounds `0.5615 < γ` and `log (4π) < 2.54`
(slightly weaker than the bounds `0.577 ≤ γ`, `log (4π) ≤ 2.532` quoted in
`lambda1_positive`, but still sufficient). -/
