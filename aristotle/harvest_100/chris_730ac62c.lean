import Mathlib
/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is nonzero whenever the
physical parameters `ħ`, `m`, `L` are nonzero. -/
theorem boxEnergy_one_ne_zero {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0)
    (hL : L ≠ 0) : boxEnergy hbar m L 1 ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  refine div_ne_zero ?_ ?_
  · simp [hpi, hh, pow_eq_zero_iff]
  · simp [hm, hL, pow_eq_zero_iff]

/-- **Infinite square well, level 3.**  The ratio of the third energy level to
the ground-state energy is `3² = 9`. -/
theorem box_level_3 {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 3 / boxEnergy hbar m L 1 = (3 : ℝ) ^ 2 := by
  have h1 : boxEnergy hbar m L 1 ≠ 0 := boxEnergy_one_ne_zero hh hm hL
  have h3 : boxEnergy hbar m L 3 = (3 : ℝ) ^ 2 * boxEnergy hbar m L 1 := by
    unfold boxEnergy
    push_cast
    ring
  rw [h3, mul_div_assoc, div_self h1, mul_one]

end QPhys

import Mathlib

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

