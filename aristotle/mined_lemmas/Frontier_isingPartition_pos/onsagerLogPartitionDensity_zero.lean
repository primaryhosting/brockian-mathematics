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

theorem onsagerLogPartitionDensity_zero :
    onsagerLogPartitionDensity 0 = Real.log 2 := by
  simp [onsagerLogPartitionDensity]

/-! ## The transfer-matrix reduction -/

/-- A configuration of a single row of the lattice. -/
abbrev RowConfig (n : ℕ) : Type := Fin (n + 1) → Bool

/-- The interaction energy (with sign convention `∑ σ σ'`) between two adjacent rows. -/
