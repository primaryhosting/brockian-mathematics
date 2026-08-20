/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology

namespace Phys

/-- The auxiliary "virial current"
`F x = x * ψ' x ^ 2 - x * (V x - E) * ψ x ^ 2 + ψ x * ψ' x`,
whose derivative is exactly `2 * ψ' x ^ 2 - x * V' x * ψ x ^ 2` for a solution of the
stationary Schrödinger equation. -/

noncomputable def virialCurrent (psi psi1 V : ℝ → ℝ) (E : ℝ) : ℝ → ℝ := fun x =>
  x * psi1 x ^ 2 - x * (V x - E) * psi x ^ 2 + psi x * psi1 x

/-- Pointwise Lagrange-type identity: for a solution of `-ψ'' + V ψ = E ψ`, the virial current
has derivative `2 ψ'² - x V' ψ²`. -/
