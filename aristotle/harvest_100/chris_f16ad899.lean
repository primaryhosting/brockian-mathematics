/-
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite potential well
("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The `n`-th level is `n²` times the ground state energy. -/
theorem boxEnergy_eq_sq_mul_boxEnergy_one (m L hbar : ℝ) (n : ℕ) :
    boxEnergy m L hbar n = (n : ℝ) ^ 2 * boxEnergy m L hbar 1 := by
  unfold boxEnergy
  push_cast
  ring

/-- The ground state energy is nonzero exactly when the mass, the width and `ħ` are nonzero. -/
theorem boxEnergy_one_ne_zero {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 1 ≠ 0 := by
  unfold boxEnergy
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  positivity

/-- **Box Level 2.** For the infinite square well, the ratio of the second energy level to the
ground state energy is `2²`, provided the ground state energy is nonzero (which rules out the
degenerate cases `m = 0`, `L = 0` or `ħ = 0`). -/
theorem box_level_2 (m L hbar : ℝ) (h : boxEnergy m L hbar 1 ≠ 0) :
    boxEnergy m L hbar 2 / boxEnergy m L hbar 1 = 2 ^ 2 := by
  rw [boxEnergy_eq_sq_mul_boxEnergy_one m L hbar 2, mul_div_assoc, div_self h]
  norm_num

/-- The same statement under the physical hypotheses `m ≠ 0`, `L ≠ 0`, `ħ ≠ 0`. -/
theorem box_level_2' {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 2 / boxEnergy m L hbar 1 = 2 ^ 2 :=
  box_level_2 m L hbar (boxEnergy_one_ne_zero hm hL hbar0)

/-- General level ratio: `Eₙ / E₁ = n²`. -/
theorem boxEnergy_ratio (m L hbar : ℝ) (n : ℕ) (h : boxEnergy m L hbar 1 ≠ 0) :
    boxEnergy m L hbar n / boxEnergy m L hbar 1 = (n : ℝ) ^ 2 := by
  rw [boxEnergy_eq_sq_mul_boxEnergy_one m L hbar n, mul_div_assoc, div_self h, mul_one]

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

