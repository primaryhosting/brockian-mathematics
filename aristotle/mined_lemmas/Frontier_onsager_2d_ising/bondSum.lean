import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

def bondSum {L : ℕ} (σ : Config L) : ℝ :=
  ∑ x : Fin L × Fin L,
    (spin σ x * spin σ (shiftIdx x.1, x.2) + spin σ x * spin σ (x.1, shiftIdx x.2))

/-- The partition function `Z_L(K) = ∑_σ exp(K ∑_{⟨x,y⟩} σ_x σ_y)` of the square-lattice
Ising model with periodic boundary conditions, where `K = βJ` is the reduced coupling.
(The Hamiltonian is `H(σ) = -J ∑_{⟨x,y⟩} σ_x σ_y`, so `Z = ∑_σ e^{-βH(σ)}`.) -/
