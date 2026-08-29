import Mathlib

/-!
# Lambda 1 Positive
Category: Riemann Program
Target: Riemann.Li.lambda1_positive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace Li

/-- Positivity of Li's first coefficient `λ₁ = 1 + γ/2 - (1/2) log (4π)`:
for all reals `g ≥ 0.577` and `L ≤ 2.532` we have `0 < 1 + g/2 - L/2`.
Applied with `g = γ` (Euler–Mascheroni) and `L = log (4π)` this gives `λ₁ > 0`. -/
theorem lambda1_positive (g L : ℝ) (hg : (0.577 : ℝ) ≤ g) (hL : L ≤ (2.532 : ℝ)) :
    0 < 1 + g / 2 - L / 2 := by
  linarith

end Li
end Riemann

