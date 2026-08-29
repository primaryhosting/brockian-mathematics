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

lemma deriv2_gauss (c : ℝ) :
    deriv (deriv (fun x : ℝ => Real.exp (c * x ^ 2)))
      = fun x : ℝ => (2 * c + 4 * c ^ 2 * x ^ 2) * Real.exp (c * x ^ 2) := by
  rw [deriv_gauss]
  funext x
  have hg : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have hl : HasDerivAt (fun x : ℝ => 2 * c * x) (2 * c) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * c))
  have h : HasDerivAt (fun y : ℝ => 2 * c * y * Real.exp (c * y ^ 2))
      (2 * c * Real.exp (c * x ^ 2) + 2 * c * x * (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1)))) x :=
    hl.mul hg
  rw [h.deriv]; ring

/-- First derivative of `x ↦ x * exp (c * x ^ 2)`. -/
