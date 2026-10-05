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

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

def isingBondSum (m n : ℕ) (σ : Fin (m + 1) × Fin (n + 1) → Bool) : ℝ :=
  ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
    (spinVal (σ (i, j)) * spinVal (σ (i + 1, j)) + spinVal (σ (i, j)) * spinVal (σ (i, j + 1)))

/-- The partition function of the 2D square-lattice Ising model on the `(m+1) × (n+1)` torus
at reduced coupling `K = βJ`. -/
