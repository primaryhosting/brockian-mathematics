/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-!
This file must literally begin with the header comment above, which Lean parses as a
module docstring; module docstrings have to precede every `import` command, so this
module is written using only Lean's core library (no `Mathlib` import) and works over
the rationals `Rat`.  The companion file `RequestProject/BoxLevel5Real.lean` states and
proves the same result over the real numbers `ℝ`, with `Real.pi` for `π`.
-/

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`
and circle constant `pi`:  `E n = n² π² ħ² / (2 m L²)`. -/
def boxEnergy (pi hbar m L : Rat) (n : Nat) : Rat :=
  (n : Rat) ^ 2 * pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- Core-library replacement for `mul_div_assoc`. -/
private theorem rat_mul_div (a b c : Rat) : a * b / c = a * (b / c) := by
  rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]

/-- The energy levels of the infinite square well scale like `n²`. -/
theorem boxEnergy_eq_sq_mul (pi hbar m L : Rat) (n : Nat) :
    boxEnergy pi hbar m L n = (n : Rat) ^ 2 * boxEnergy pi hbar m L 1 := by
  unfold boxEnergy
  have h1 : ((1 : Nat) : Rat) ^ 2 = 1 := by decide
  rw [h1, Rat.one_mul, Rat.mul_assoc, rat_mul_div, rat_mul_div]

/-- Dividing a multiple of a nonzero rational by that rational. -/
private theorem rat_mul_div_cancel (a x : Rat) (hx : x ≠ 0) : a * x / x = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel x hx, Rat.mul_one]

/-- **Box, level 5.**  For a particle in a one-dimensional infinite potential well with
nonvanishing ground-state energy, the ratio of the fifth energy level to the ground state
is `5² = 25`. -/
theorem box_level_5 (pi hbar m L : Rat) (h : boxEnergy pi hbar m L 1 ≠ 0) :
    boxEnergy pi hbar m L 5 / boxEnergy pi hbar m L 1 = 5 ^ 2 := by
  have h5 : ((5 : Nat) : Rat) ^ 2 = 5 ^ 2 := by decide
  rw [boxEnergy_eq_sq_mul pi hbar m L 5, h5, rat_mul_div_cancel _ _ h]

end QPhys

import Mathlib

/-!
# Box Level 5 (real-valued version)

Category: Quantum Physics
Provenance: Aristotle theorem prover (Harmonic)

Companion to `RequestProject/BoxLevel5.lean`: the same statement, over `ℝ` and with the
genuine circle constant `Real.pi`.
-/

namespace QPhys

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional infinite
potential well of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- **Box, level 5, over `ℝ`.**  For a particle in a one-dimensional infinite potential
well with nonzero mass, width and `hbar`, the ratio of the fifth energy level to the
ground state is `5² = 25`. -/
theorem box_level_5_real (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 5 / boxEnergyReal hbar m L 1 = 5 ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  field_simp
  ring

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

