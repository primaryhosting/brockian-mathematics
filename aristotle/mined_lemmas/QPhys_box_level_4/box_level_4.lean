import Mathlib

/-!
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
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

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
(particle in a box) of width `L`:  `Eₙ = n² π² ħ² / (2 m L²)`, for `n = 1, 2, 3, …`. -/

theorem box_level_4 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 4 / boxEnergy hbar m L 1 = (4 : ℝ) ^ 2 := by
  simpa using boxEnergy_div_boxEnergy_one hbar m L hhbar hm hL 4

/-- Product form of the level-4 relation: `E₄ = 4² · E₁`.  Unlike the ratio statement, this
holds unconditionally (no nonvanishing assumptions are needed). -/
