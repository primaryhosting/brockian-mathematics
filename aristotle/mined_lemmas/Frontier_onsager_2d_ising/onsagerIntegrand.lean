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

/-- The argument of the logarithm in Onsager's exact free energy formula for the
two-dimensional square-lattice Ising model with reduced coupling `K = βJ`. -/

noncomputable def onsagerIntegrand (K t₁ t₂ : ℝ) : ℝ :=
  Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos t₁ + Real.cos t₂)

/-- Onsager's exact (dimensionless) free energy per site
`-βf = log 2 + (8π²)⁻¹ ∫₀^{2π} ∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₂ dθ₁`
for the two-dimensional square-lattice Ising model at reduced coupling `K = βJ`. -/
