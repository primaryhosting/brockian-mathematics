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

/-! ## The 2D square-lattice Ising model on an `L × L` torus -/

/-- The real spin value `±1` attached to a Boolean spin variable. -/

noncomputable def onsagerArg (β θ₁ θ₂ : ℝ) : ℝ :=
  Real.cosh (2 * β) ^ 2 - Real.sinh (2 * β) * (Real.cos θ₁ + Real.cos θ₂)

/-- Onsager's exact free-energy density, in the form of the limiting value of
`N⁻¹ log Z_N(β)`:
`log 2 + (8π²)⁻¹ ∫₀^{2π} ∫₀^{2π} log (cosh²(2β) - sinh(2β)(cos θ₁ + cos θ₂)) dθ₂ dθ₁`. -/
