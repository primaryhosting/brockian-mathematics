/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

noncomputable def onsagerFreeEnergy (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (2 * (2 * Real.pi) ^ 2)) *
    ∫ θ₁ in (0 : ℝ)..(2 * Real.pi), ∫ θ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ₁ + Real.cos θ₂))

/-- The classical single-integral form of Onsager's free energy, obtained from the
double integral by performing one of the two angular integrations. -/
