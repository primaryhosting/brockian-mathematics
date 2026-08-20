/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

namespace Frontier

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

def Admissible {N : ℕ} (ψ : Fin N → Space → ℂ) : Prop :=
  (∀ i, Differentiable ℝ (ψ i)) ∧ (∀ i, Integrable (gradSqNorm (ψ i))) ∧ L2Orthonormal ψ

/-- **The Lieb–Thirring kinetic energy inequality** with constant `Kc`: for every finite
orthonormal family of (differentiable) one-particle wave functions, the total kinetic
energy dominates `Kc ∫ ρ^{5/3}`, where `ρ` is the associated one-particle density.
This is the fermionic (Pauli-principle) strengthening of the Sobolev inequality; it is the
deep analytic input of the Lieb–Thirring proof of stability of matter, and is taken here as
a hypothesis. -/
