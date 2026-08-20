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

def spin (b : Bool) : ℝ := if b then 1 else -1

/-- A spin configuration on the `(n+1) × (n+1)` square lattice with periodic
boundary conditions (a discrete torus). -/
abbrev Config (n : ℕ) : Type := Fin (n + 1) × Fin (n + 1) → Bool

/-- The sum `∑_{⟨x,y⟩} σ_x σ_y` over all nearest-neighbour bonds of the periodic
`(n+1) × (n+1)` square lattice.  Each site contributes the bond to its right
neighbour and the bond to the neighbour below it, so every bond is counted once. -/

def bondSum {n : ℕ} (σ : Config n) : ℝ :=
  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
    (spin (σ (i, j)) * spin (σ (i + 1, j)) + spin (σ (i, j)) * spin (σ (i, j + 1)))

/-- The partition function `Z_N(K) = ∑_σ exp (K ∑_{⟨x,y⟩} σ_x σ_y)` of the
two-dimensional Ising model on the periodic `(n+1) × (n+1)` lattice, at reduced
coupling `K = β J`. -/

noncomputable def isingPartition (n : ℕ) (K : ℝ) : ℝ :=
  ∑ σ : Config n, Real.exp (K * bondSum σ)

/-- The free energy density in the form `(1 / N²) log Z_N(K)`, i.e. `-β f_N(K)`. -/

theorem isingPartition_pos (n : ℕ) (K : ℝ) : 0 < isingPartition n K := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- The single-site lattice: both configurations have bond sum `2` (the site is its own
neighbour in both directions), so `Z₁(K) = 2 e^{2K}`. -/
