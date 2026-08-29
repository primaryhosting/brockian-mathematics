import Mathlib
-- (Lean requires `import` to precede any module documentation, so the required
-- header comment appears immediately below the import.)
/-!
# Box Level 6
Category: Quantum Physics
Target: QPhys.box_level_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`, with
reduced Planck constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- General level ratio for the infinite square well: `E_n / E_1 = n²`. -/
theorem boxEnergy_ratio (hbar m L : ℝ) (n : ℕ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  field_simp
  ring

/-- For the infinite square well, the ratio of the sixth energy level to the
ground-state energy is `6² = 36`. -/
theorem box_level_6 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 6 / boxEnergy hbar m L 1 = (6 : ℝ) ^ 2 := by
  simpa using boxEnergy_ratio hbar m L 6 hhbar hm hL

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

