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

/-- The real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

def energy {m n : ℕ} (J : ℝ) (σ : Fin m × Fin n → Bool) : ℝ :=
  -J * ∑ i : Fin m, ∑ j : Fin n,
      (spin (σ (i, j)) * spin (σ (nextIdx i, j)) + spin (σ (i, j)) * spin (σ (i, nextIdx j)))

/-- The canonical partition function of the 2D Ising model on the `m × n` torus
at inverse temperature `β` and coupling `J`. -/
