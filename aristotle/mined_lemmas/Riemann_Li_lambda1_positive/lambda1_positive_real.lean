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

theorem lambda1_positive_real :
    0 < 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2 := by
  have h1 := eulerMascheroniConstant_gt
  have h2 := log_four_pi_lt
  norm_num at h1 h2 ⊢
  linarith

end Riemann.Li

