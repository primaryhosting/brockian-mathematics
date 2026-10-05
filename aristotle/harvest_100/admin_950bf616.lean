/-!
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean requires every `import` to precede all other
commands, so a file that must *begin* with the header comment above cannot
carry an `import Mathlib` line.  This module therefore uses only Lean core
(`Rat`), which suffices for the statement.  A real-valued version of the same
statement, using the physical formula `Eₙ = n²π²ħ²/(2mL²)` and Mathlib's
`div_self`, is proved in `RequestProject/QPhysReal.lean`.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle in a one-dimensional
infinite potential well ("particle in a box"), measured in units in which the
ground-state energy is `E₁`: `Eₙ = n² E₁`. -/
def boxEnergy (E1 : Rat) (n : Nat) : Rat := (n : Rat) ^ 2 * E1

@[simp] theorem boxEnergy_one (E1 : Rat) : boxEnergy E1 1 = E1 := by
  have h : ((1 : Nat) : Rat) ^ 2 = 1 := rfl
  rw [boxEnergy, h, Rat.one_mul]

/-- The infinite-well energy ratio `E₁ / E₁ = 1²`, for a nonzero ground-state
energy `E₁`. -/
theorem box_level_1 (E1 : Rat) (hE1 : E1 ≠ 0) :
    boxEnergy E1 1 / boxEnergy E1 1 = (1 : Rat) ^ 2 := by
  have hpow : (1 : Rat) ^ 2 = 1 := rfl
  rw [boxEnergy_one, hpow, Rat.div_def, Rat.mul_inv_cancel E1 hE1]

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

import Mathlib

/-!
# Box Level 1 (real-valued companion)

Real-valued version of `QPhys.box_level_1`, using the physical energy formula
for a particle in a one-dimensional infinite well,
`Eₙ = n² π² ħ² / (2 m L²)`.  The key Mathlib lemma is `div_self`.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite potential well of width `L`, with reduced Planck
constant `hbar`: `Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

theorem boxEnergyReal_one_pos {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hbar_ne : hbar ≠ 0) : 0 < boxEnergyReal m L hbar 1 := by
  have hh : 0 < hbar ^ 2 := by positivity
  unfold boxEnergyReal
  have h1 : ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
  rw [h1]
  positivity

/-- The infinite-well energy ratio `E₁ / E₁ = 1²`. -/
theorem box_level_1_real (m L hbar : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hbar_ne : hbar ≠ 0) :
    boxEnergyReal m L hbar 1 / boxEnergyReal m L hbar 1 = (1 : ℝ) ^ 2 := by
  rw [div_self (boxEnergyReal_one_pos hm hL hbar_ne).ne', one_pow]

end QPhys

