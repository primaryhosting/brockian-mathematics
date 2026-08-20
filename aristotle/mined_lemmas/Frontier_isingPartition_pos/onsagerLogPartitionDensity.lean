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

noncomputable def onsagerLogPartitionDensity (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (2 * π) ^ 2) *
    ∫ t₁ in (0 : ℝ)..(2 * π), ∫ t₂ in (0 : ℝ)..(2 * π),
      Real.log (Real.cosh (2 * K) ^ 2
        - Real.sinh (2 * K) * (Real.cos t₁ + Real.cos t₂))

/-- The partition function is positive, so the free energy density is well defined. -/
