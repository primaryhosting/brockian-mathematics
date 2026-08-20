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

theorem isingPartition_pos (n : ℕ) (K : ℝ) : 0 < isingPartition n K := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- The single-site lattice: both configurations have bond sum `2` (the site is its own
neighbour in both directions), so `Z₁(K) = 2 e^{2K}`. -/
