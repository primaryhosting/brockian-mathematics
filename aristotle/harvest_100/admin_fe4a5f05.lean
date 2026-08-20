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
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- For the infinite square well, the ratio of the `n`-th energy level to the ground state
energy is `n²`. -/
theorem boxEnergy_div_boxEnergy_one (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L)
    (n : ℕ) : boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hden : (2 : ℝ) * m * L ^ 2 ≠ 0 := by positivity
  unfold boxEnergy
  rw [div_div_div_cancel_right₀]
  · push_cast
    field_simp
  · exact hden

/-- **Infinite square well, level 4.** The ratio of the fourth energy level to the ground
state energy is `4² = 16`. -/
theorem box_level_4 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 4 / boxEnergy hbar m L 1 = (4 : ℝ) ^ 2 := by
  simpa using boxEnergy_div_boxEnergy_one hbar m L hhbar hm hL 4

/-- Product form of the level-4 relation: `E₄ = 4² · E₁`.  Unlike the ratio statement, this
holds unconditionally (no nonvanishing assumptions are needed). -/
theorem box_level_4_mul (hbar m L : ℝ) :
    boxEnergy hbar m L 4 = (4 : ℝ) ^ 2 * boxEnergy hbar m L 1 := by
  unfold boxEnergy
  push_cast
  ring

end QPhys

