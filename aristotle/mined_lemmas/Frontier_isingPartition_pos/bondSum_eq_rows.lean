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

theorem bondSum_eq_rows {n : ℕ} (σ : Config n) :
    bondSum σ = ∑ i : Fin (n + 1),
      (rowCoupling (fun j => σ (i, j)) (fun j => σ (i + 1, j))
        + rowInternal (fun j => σ (i, j))) := by
  rw [bondSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_add_distrib]
  rfl

/-- **Transfer-matrix reduction.**  The partition function of the periodic
`(n+1) × (n+1)` Ising lattice is the trace of the `(n+1)`-st power of the
transfer matrix. -/
