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

lemma deriv2_xgauss (c : ℝ) :
    deriv (deriv (fun x : ℝ => x * Real.exp (c * x ^ 2)))
      = fun x : ℝ => (6 * c * x + 4 * c ^ 2 * x ^ 3) * Real.exp (c * x ^ 2) := by
  rw [deriv_xgauss]
  funext x
  have hg : HasDerivAt (fun x : ℝ => Real.exp (c * x ^ 2))
      (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1))) x :=
    (((hasDerivAt_pow 2 x).const_mul c).exp)
  have hl : HasDerivAt (fun x : ℝ => 1 + 2 * c * x ^ 2) (2 * c * (2 * x ^ 1)) x := by
    simpa using (((hasDerivAt_pow 2 x).const_mul (2 * c)).const_add 1)
  have h : HasDerivAt (fun y : ℝ => (1 + 2 * c * y ^ 2) * Real.exp (c * y ^ 2))
      (2 * c * (2 * x ^ 1) * Real.exp (c * x ^ 2)
        + (1 + 2 * c * x ^ 2) * (Real.exp (c * x ^ 2) * (c * (2 * x ^ 1)))) x :=
    hl.mul hg
  rw [h.deriv]; ring

/-! ## The Landau problem

A particle of mass `m` and charge `q` in a uniform magnetic field `B` (say along the `z`-axis)
moves, after separation of variables in the Landau gauge, according to a one-dimensional
harmonic oscillator with the cyclotron frequency `ω_c = q * B / m`:
`H ψ = -(ℏ² / (2 m)) ψ'' + (1/2) m ω_c² x² ψ`.
Its spectrum is `E n = ℏ ω_c (n + 1/2)`.
-/

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/
