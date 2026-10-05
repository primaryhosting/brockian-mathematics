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
(a "particle in a box") of width `L`, with reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The infinite-well energy ratio `E₂ / E₁ = 2²`. -/
theorem box_level_2 (hbar m L : ℝ) (hbar_pos : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 2 / boxEnergy hbar m L 1 = (2 : ℝ) ^ 2 := by
  have hden : (2 * m * L ^ 2) ≠ 0 := by positivity
  have h1 : boxEnergy hbar m L 1 ≠ 0 := by
    unfold boxEnergy
    have : (0 : ℝ) < (1 : ℕ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2) := by
      positivity
    exact ne_of_gt this
  unfold boxEnergy at h1 ⊢
  field_simp at h1 ⊢
  ring

end QPhys

