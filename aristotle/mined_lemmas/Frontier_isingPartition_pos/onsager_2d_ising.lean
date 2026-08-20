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

theorem onsager_2d_ising :
    (∀ (n : ℕ) (K : ℝ), 0 < isingPartition n K) ∧
    (∀ (n : ℕ) (K : ℝ),
        isingPartition n K = Matrix.trace (transferMatrix n K ^ (n + 1))) ∧
    (∀ n : ℕ, isingPartition n 0 = 2 ^ ((n + 1) ^ 2)) ∧
    onsagerLogPartitionDensity 0 = Real.log 2 ∧
    Filter.Tendsto (fun n : ℕ => logPartitionDensity n 0) Filter.atTop
      (nhds (onsagerLogPartitionDensity 0)) := by
  refine ⟨isingPartition_pos, isingPartition_eq_trace_transferMatrix, isingPartition_zero,
    onsagerLogPartitionDensity_zero, ?_⟩
  rw [onsagerLogPartitionDensity_zero]
  simp only [logPartitionDensity_zero]
  exact tendsto_const_nhds

end Frontier

