/-!
# Lambda 1 Positive
Category: Riemann Program
Target: Riemann.Li.lambda1_positive
Statement: For all real g, L with 0.577 <= g and L <= 2.532, we have 0 < 1 + g/2 - L/2. This is the positivity of Li's first coefficient lambda_1 = 1 + gamma/2 - (1/2) log(4*pi) (with gamma >= 0.577 the Euler-Mascheroni constant and log(4*pi) <= 2.532); Li's criterion states RH holds iff lambda_n >= 0 for all n >= 1.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Li

/-- Positivity of Li's first coefficient `λ₁ = 1 + γ/2 - (1/2) log (4π)`:
for real `g, L` with `0.577 ≤ g` and `L ≤ 2.532`, we have `0 < 1 + g/2 - L/2`.
Here `g` stands for a lower bound on the Euler–Mascheroni constant `γ` and
`L` for an upper bound on `log (4π)`. -/
theorem lambda1_positive (g L : ℝ) (hg : (0.577 : ℝ) ≤ g) (hL : L ≤ (2.532 : ℝ)) :
    0 < 1 + g / 2 - L / 2 := by
  linarith

end Riemann.Li

