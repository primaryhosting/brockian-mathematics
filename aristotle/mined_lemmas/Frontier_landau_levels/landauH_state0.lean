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

lemma landauH_state0 (m omega hbar : ℝ) (hm : m ≠ 0) (hbar0 : hbar ≠ 0) (x : ℝ) :
    landauH m omega hbar (landauState0 m omega hbar) x
      = landauEnergy hbar omega 0 * landauState0 m omega hbar x := by
  unfold landauH landauState0 landauEnergy
  rw [deriv2_gauss]
  field_simp
  ring

/-- `ψ₁` is an eigenfunction of the Landau Hamiltonian with eigenvalue `3 ℏ ω_c / 2`. -/
