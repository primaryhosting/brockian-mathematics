import Mathlib

/-!
# Box Level 3 (real-valued companion)

A real-number version of `QPhys.box_level_3`, with the physical constants
`ħ`, the particle mass `m` and the well width `L` written out explicitly.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well of width `L`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the infinite square well with the explicit constants `ħ`, `m`, `L`, the
ratio of the third energy level to the ground-state energy is `3² = 9`. -/
theorem box_level_3_real (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 3 / boxEnergyReal hbar m L 1 = (3 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  push_cast
  rw [div_div_div_eq]
  field_simp

end QPhys

/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle in a one-dimensional
infinite square well ("particle in a box"), expressed in terms of the
ground-state energy `E₁ = π²ħ²/(2mL²)`:

`E n = n² * E₁`.

The dependence on `ħ`, the mass `m` and the well width `L` is entirely carried
by `E₁`, so the level ratios do not depend on them. -/
def boxEnergy (E₁ : Rat) (n : Nat) : Rat := (n : Rat) ^ 2 * E₁

/-- For the infinite square well, the ratio of the third energy level to the
ground-state energy is `3² = 9`. -/
theorem box_level_3 (E₁ : Rat) (hE : E₁ ≠ 0) :
    boxEnergy E₁ 3 / boxEnergy E₁ 1 = 3 ^ 2 := by
  show ((9 : Rat) * E₁) / ((1 : Rat) * E₁) = 9
  rw [Rat.one_mul, Rat.mul_div_cancel hE]

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

