/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Gaussian derivative computations -/

/-- First derivative of a Gaussian `x ↦ exp (c * x ^ 2)`. -/

lemma deriv_xgauss (c : ℝ) :
    deriv (fun x : ℝ => x * Real.exp (c * x ^ 2))
      = fun x : ℝ => (1 + 2 * c * x ^ 2) * Real.exp (c * x ^ 2) := by
  funext x
  have hg : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have h : HasDerivAt (fun y : ℝ => y * Real.exp (c * y ^ 2))
      (1 * Real.exp (c * x ^ 2) + x * (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1)))) x :=
    (hasDerivAt_id x).mul hg
  rw [h.deriv]; ring

/-- Second derivative of `x ↦ x * exp (c * x ^ 2)`. -/
