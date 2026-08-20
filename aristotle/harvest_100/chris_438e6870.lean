import Mathlib

/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
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
(the "particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For a particle in a one-dimensional infinite square well, the ratio of the third
energy level to the ground-state energy is `3² = 9`. -/
theorem box_level_3 (m L hbar : ℝ) (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    boxEnergy m L hbar 3 / boxEnergy m L hbar 1 = (3 : ℝ) ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : boxEnergy m L hbar 1 ≠ 0 := by
    have : (0 : ℝ) < boxEnergy m L hbar 1 := by
      unfold boxEnergy
      positivity
    exact ne_of_gt this
  unfold boxEnergy at h1 ⊢
  rw [div_div_div_cancel_right₀]
  · field_simp
    ring
  · positivity

end QPhys

