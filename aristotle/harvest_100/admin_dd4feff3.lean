/-
/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- The requested header is reproduced verbatim above, quoted inside a comment: Lean 4 requires
-- `import` commands to come first in a file, so a module docstring cannot precede them.
-- It is repeated below in its legal position, immediately after the imports.
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

/-- Energy levels of a particle of mass `m` confined to a one-dimensional infinite
potential well (a "box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- General level ratio for the infinite square well: `E n / E 1 = n²`. -/
theorem boxEnergy_div_boxEnergy_one (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : 0 < m)
    (hL : 0 < L) (n : ℕ) : boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hden : (2 : ℝ) * m * L ^ 2 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  rw [div_div_div_cancel_right₀]
  · field_simp
    norm_num
  · exact hden

/-- **Infinite square well, level 2.** For a particle of positive mass `m` in a box of
positive width `L` (with nonzero reduced Planck constant `ħ`), the ratio of the second
energy level to the ground-state energy is `2² = 4`. -/
theorem box_level_2 (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 2 / boxEnergy hbar m L 1 = 2 ^ 2 := by
  simpa using boxEnergy_div_boxEnergy_one hbar m L hbar_ne hm hL 2

end QPhys

