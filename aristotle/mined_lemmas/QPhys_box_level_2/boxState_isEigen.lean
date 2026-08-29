import Mathlib

/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
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

/-- The `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`, up to normalization:
`ψ_n(x) = sin (n π x / L)`.  It vanishes at both walls `x = 0` and `x = L`. -/

theorem boxState_isEigen (hbar m L : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) (n : ℕ) (x : ℝ) :
    -hbar ^ 2 / (2 * m) * deriv (deriv (boxState L n)) x
      = boxEnergy hbar m L n * boxState L n x := by
  have hb : boxState L n = fun y : ℝ => Real.sin ((n : ℝ) * Real.pi / L * y) := rfl
  have h := deriv_deriv_sin_mul ((n : ℝ) * Real.pi / L) x
  rw [hb, h]
  simp only [boxEnergy]
  field_simp

/-- **Box Level 2.**  For a particle in a one-dimensional infinite square well,
the ratio of the second energy level to the ground state energy is `2² = 4`. -/
