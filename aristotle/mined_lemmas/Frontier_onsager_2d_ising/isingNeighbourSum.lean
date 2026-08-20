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

noncomputable def isingNeighbourSum (m n : ℕ) [NeZero m] [NeZero n]
    (σ : ZMod m × ZMod n → Bool) : ℝ :=
  ∑ x : ZMod m × ZMod n,
    (spin (σ x) * spin (σ (x.1 + 1, x.2)) + spin (σ x) * spin (σ (x.1, x.2 + 1)))

/-- The Ising partition function `Z = ∑_σ exp (K ∑_{⟨x,y⟩} σ_x σ_y)` on the `m × n` torus. -/
