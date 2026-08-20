/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file must literally *begin* with the header comment above, so it cannot contain any
`import` command (Lean requires imports to be the very first commands of a file).  It is
therefore written against the Lean core prelude only, with the numeric parameters taken in
`Rat`.  The companion file `RequestProject/Main.lean` develops the same statement over `ℝ`
with `Real.pi` and the reduced Planck constant (`QPhys.box_level_5_real`).
-/

namespace QPhys

/-! ### Small arithmetic helpers (core `Rat` only) -/

theorem rat_inv_ne_zero {a : Rat} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hinv
  have h1 : a * a⁻¹ = 1 := Rat.mul_inv_cancel a ha
  rw [hinv, Rat.mul_zero] at h1
  exact absurd h1.symm (by decide)

theorem rat_mul_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  rcases Rat.mul_eq_zero.mp hab with h | h
  · exact ha h
  · exact hb h

theorem rat_div_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [Rat.div_def]
  exact rat_mul_ne_zero ha (rat_inv_ne_zero hb)

/-! ### The infinite square well -/

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
("particle in a box") of width `L`, written with Planck's constant `h`:

`Eₙ = n² h² / (8 m L²)`.

(Equivalently `Eₙ = n² π² ħ² / (2 m L²)` with `ħ = h / (2π)`; see
`QPhys.box_level_5_real` in `RequestProject/Main.lean` for that form over `ℝ`.) -/
def boxEnergy (h m L : Rat) (n : Nat) : Rat :=
  (n : Rat) * (n : Rat) * (h * h) / (8 * m * (L * L))

/-- The ground-state energy of the well is nonzero as soon as `h`, `m` and `L` are. -/
theorem boxEnergy_one_ne_zero {h m L : Rat} (hh : h ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy h m L 1 ≠ 0 := by
  have h8 : (8 : Rat) ≠ 0 := by decide
  unfold boxEnergy
  refine rat_div_ne_zero ?_ (rat_mul_ne_zero (rat_mul_ne_zero h8 hm) (rat_mul_ne_zero hL hL))
  rw [show ((1 : Nat) : Rat) = 1 from by decide, Rat.one_mul, Rat.one_mul]
  exact rat_mul_ne_zero hh hh

/-- **Box level 5.**  For a particle in a one-dimensional infinite square well, the ratio of the
fifth energy level to the ground-state energy equals `5² = 25`, independently of the mass `m`,
the width `L` and Planck's constant `h`. -/
theorem box_level_5 {h m L : Rat} (hh : h ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy h m L 5 / boxEnergy h m L 1 = (5 : Rat) ^ 2 := by
  have hx : boxEnergy h m L 1 ≠ 0 := boxEnergy_one_ne_zero hh hm hL
  have hfive : boxEnergy h m L 5 = (5 : Rat) ^ 2 * boxEnergy h m L 1 := by
    unfold boxEnergy
    rw [show ((5 : Nat) : Rat) = 5 from by decide,
      show ((1 : Nat) : Rat) = 1 from by decide,
      Rat.one_mul, Rat.one_mul,
      Rat.pow_succ, Rat.pow_succ, Rat.pow_zero, Rat.one_mul,
      Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_assoc]
  rw [hfive, Rat.mul_div_cancel hx]

end QPhys

import Mathlib

/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The target theorem `QPhys.box_level_5` itself lives in `RequestProject/BoxLevel5.lean`, which
begins with the required header comment and therefore cannot contain any `import`.  This file
records the same physics over the reals, with `Real.pi` and the reduced Planck constant `ħ`:
`QPhys.box_level_5_real`.
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
("particle in a box") of width `L`, in terms of the reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the real infinite well is nonzero when `ħ`, `m` and `L` are. -/
theorem boxEnergyReal_one_ne_zero {hbar m L : ℝ} (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 1 ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  push_cast
  rw [one_pow, one_mul]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hpi) (pow_ne_zero 2 hhbar))
    (mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero 2 hL))

/-- **Box level 5, over the reals.**  For the one-dimensional infinite square well the ratio of
the fifth energy level to the ground-state energy is `5² = 25`, independently of `ħ`, `m`, `L`. -/
theorem box_level_5_real {hbar m L : ℝ} (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 5 / boxEnergyReal hbar m L 1 = (5 : ℝ) ^ 2 := by
  have hx : boxEnergyReal hbar m L 1 ≠ 0 := boxEnergyReal_one_ne_zero hhbar hm hL
  have h5 : boxEnergyReal hbar m L 5 = (5 : ℝ) ^ 2 * boxEnergyReal hbar m L 1 := by
    unfold boxEnergyReal
    push_cast
    ring
  rw [h5, mul_div_assoc, div_self hx, mul_one]

end QPhys

