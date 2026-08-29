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

lemma deriv_gauss (c : ℝ) :
    deriv (fun x : ℝ => Real.exp (c * x ^ 2)) = fun x : ℝ => 2 * c * x * Real.exp (c * x ^ 2) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have := h.deriv
  rw [this]; ring

/-- Second derivative of a Gaussian `x ↦ exp (c * x ^ 2)`. -/
