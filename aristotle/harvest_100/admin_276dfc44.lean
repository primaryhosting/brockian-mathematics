import Mathlib
/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the single `import Mathlib` line above must come first.

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- Every level is `n²` times the ground state energy. -/
theorem boxEnergy_eq_sq_mul_boxEnergy_one (m L hbar : ℝ) (n : ℕ) :
    boxEnergy m L hbar n = (n : ℝ) ^ 2 * boxEnergy m L hbar 1 := by
  unfold boxEnergy
  norm_num
  ring

/-- For the infinite square well, the ratio of the second energy level to the
ground state energy is `2² = 4`, provided the ground state energy is nonzero
(equivalently, the mass, the well width and `ħ` are all nonzero). -/
theorem box_level_2 (m L hbar : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 2 / boxEnergy m L hbar 1 = 2 ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : boxEnergy m L hbar 1 ≠ 0 := by
    unfold boxEnergy
    norm_num [hm, hL, hbar0, hpi]
  rw [boxEnergy_eq_sq_mul_boxEnergy_one m L hbar 2, mul_div_assoc, div_self h1, mul_one]
  norm_num

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

