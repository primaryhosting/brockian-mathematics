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

theorem boxState_width (L : ℝ) (hL : L ≠ 0) (n : ℕ) : boxState L n L = 0 := by
  have : (n : ℝ) * Real.pi / L * L = (n : ℝ) * Real.pi := by
    field_simp
  simp [boxState, this, Real.sin_nat_mul_pi]

/-- Second derivative of a sine wave. -/
