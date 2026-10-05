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

lemma landauH_state1 (m omega hbar : ℝ) (hm : m ≠ 0) (hbar0 : hbar ≠ 0) (x : ℝ) :
    landauH m omega hbar (landauState1 m omega hbar) x
      = landauEnergy hbar omega 1 * landauState1 m omega hbar x := by
  unfold landauH landauState1 landauEnergy
  rw [deriv2_xgauss]
  field_simp
  ring

/-- **Landau levels.**  For a particle of mass `m > 0` and charge `q` in a uniform magnetic
field `B`, with cyclotron frequency `ω_c = q B / m`, the energy levels are
`E n = ℏ ω_c (n + 1/2)`:

* consecutive levels are equally spaced by `ℏ ω_c`;
* the ground state `ψ₀ x = exp (-m ω_c x² / (2ℏ))` solves the stationary Schrödinger equation
  with energy `E 0 = ℏ ω_c / 2`;
* the first excited state `ψ₁ x = x ψ₀ x` solves it with energy `E 1 = 3 ℏ ω_c / 2`.
-/
