import Mathlib

/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
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

/-- The ground-state energy of the infinite well is nonzero whenever the
physical parameters `ħ`, `m`, `L` are nonzero. -/
theorem boxEnergy_one_ne_zero {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0)
    (hL : L ≠ 0) : boxEnergy hbar m L 1 ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  simp only [ne_eq, div_eq_zero_iff, not_or]
  refine ⟨by positivity, by positivity⟩

/-- **Box Level 7.** For a particle in a one-dimensional infinite square well,
the ratio of the seventh energy level to the ground-state energy equals `7² = 49`. -/
theorem box_level_7 {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 7 / boxEnergy hbar m L 1 = (7 : ℝ) ^ 2 := by
  have h1 : boxEnergy hbar m L 1 ≠ 0 := boxEnergy_one_ne_zero hh hm hL
  rw [div_eq_iff h1]
  unfold boxEnergy
  push_cast
  ring

end QPhys

