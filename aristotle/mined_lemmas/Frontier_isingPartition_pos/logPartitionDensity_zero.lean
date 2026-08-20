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

theorem logPartitionDensity_zero (n : ℕ) :
    logPartitionDensity n 0 = Real.log 2 := by
  have hn : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  rw [logPartitionDensity, isingPartition_zero, Real.log_pow]
  push_cast
  field_simp

/-- Onsager's expression at `K = 0` collapses to `log 2`. -/
