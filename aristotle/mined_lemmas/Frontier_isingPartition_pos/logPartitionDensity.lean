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

set_option grind.warning false

namespace Frontier

/-! ## The two-dimensional Ising model on a periodic square lattice -/

/-- The real spin value attached to a Boolean spin variable: `true ↦ +1`, `false ↦ -1`. -/

noncomputable def logPartitionDensity (n : ℕ) (K : ℝ) : ℝ :=
  Real.log (isingPartition n K) / ((n + 1 : ℝ) ^ 2)

/-- Onsager's exact expression for the infinite-volume free energy density
`-β f(K)` of the two-dimensional Ising model:
`log 2 + (2π)⁻² ∫₀^{2π} ∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₂ dθ₁`. -/
