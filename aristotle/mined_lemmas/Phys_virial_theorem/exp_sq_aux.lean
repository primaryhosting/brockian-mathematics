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

private theorem exp_sq_aux (x : ℝ) : (Real.exp (-x ^ 2 / 2)) ^ 2 = Real.exp (-1 * x ^ 2) := by
  rw [sq, ← Real.exp_add]; ring_nf

