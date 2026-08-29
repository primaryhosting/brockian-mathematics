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

noncomputable def landauState1 (m omega hbar : ℝ) : ℝ → ℝ :=
  fun x => x * Real.exp (-(m * omega) / (2 * hbar) * x ^ 2)

/-- `ψ₀` is an eigenfunction of the Landau Hamiltonian with eigenvalue `ℏ ω_c / 2`. -/
