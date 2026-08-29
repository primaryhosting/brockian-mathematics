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

import Mathlib
/-!
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
(box) of width `L`: `E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- **Box Level 1.** For a particle in an infinite square well with nonzero ground-state
energy, the ratio of the ground-state energy to itself equals `1² = 1`: the `n = 1` case
of the general level formula `E n / E 1 = n²`. -/
theorem box_level_1 (hbar m L : ℝ) (h : boxEnergy hbar m L 1 ≠ 0) :
    boxEnergy hbar m L 1 / boxEnergy hbar m L 1 = (1 : ℝ) ^ 2 := by
  rw [div_self h, one_pow]

/-- The general level-ratio formula: `E n / E 1 = n²` whenever the ground-state energy is
nonzero. `box_level_1` is the special case `n = 1`. -/
theorem box_level_ratio (hbar m L : ℝ) (n : ℕ) (h : boxEnergy hbar m L 1 ≠ 0) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have key : ∀ k : ℕ, boxEnergy hbar m L k
      = (k : ℝ) ^ 2 * ((Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)) := by
    intro k
    rw [boxEnergy, mul_div_assoc]
  have hc : (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2) ≠ 0 := by
    intro hcc
    apply h
    rw [key 1, hcc, mul_zero]
  rw [key n, key 1, Nat.cast_one, one_pow, one_mul, mul_div_assoc, div_self hc, mul_one]

end QPhys

