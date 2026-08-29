import Mathlib

/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
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

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`,
with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground state energy of the infinite well is positive when `ħ, m, L > 0`. -/
theorem boxEnergy_one_pos {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    0 < boxEnergy hbar m L 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  unfold boxEnergy
  positivity

/-- **Box Level 5**: for a particle in a one-dimensional infinite square well,
the ratio of the fifth energy level to the ground-state energy is `5² = 25`. -/
theorem box_level_5 {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 5 / boxEnergy hbar m L 1 = (5 : ℝ) ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hden : (2 : ℝ) * m * L ^ 2 ≠ 0 := by positivity
  have h1 : boxEnergy hbar m L 1 ≠ 0 := ne_of_gt (boxEnergy_one_pos hhbar hm hL)
  unfold boxEnergy at h1 ⊢
  push_cast
  field_simp at h1 ⊢

end QPhys

