/-!
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the shape of this file: Lean 4 requires every `import` command to come before any
other command, including a module docstring.  Since the header comment above must literally
be the first thing in the file, this file cannot import Mathlib, and is therefore developed
in plain Lean 4 core over the rationals, with the energy scale `c = π²ℏ²/(2mL²)` of the well
kept as a parameter.  The fully explicit real-valued companion statement (with `π`, `ℏ`, the
mass `m` and the width `L` spelled out over `ℝ`) is proved as `QPhys.box_level_4_real` in
`RequestProject/BoxLevel4Real.lean`.
-/

namespace QPhys

/-- Energy levels of a particle in a one-dimensional infinite square well
("particle in a box"):  `Eₙ = n² · c`, where `c = π²ℏ²/(2mL²)` is the energy scale of the
well (so `c = E₁` is the ground-state energy). -/
def boxEnergy (c : Rat) (n : Nat) : Rat := (n : Rat) ^ 2 * c

/-- **Infinite-well energy ratio.**  For a particle in a one-dimensional infinite square
well with nonzero energy scale `c`, the fourth energy level is `4² = 16` times the
ground-state energy:  `E₄ / E₁ = 4²`. -/
theorem box_level_4 (c : Rat) (hc : c ≠ 0) :
    boxEnergy c 4 / boxEnergy c 1 = 4 ^ 2 := by
  show (16 : Rat) * c / ((1 : Rat) * c) = 16
  rw [Rat.one_mul, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hc, Rat.mul_one]

end QPhys

import Mathlib

/-!
# Box Level 4 — real-valued companion

Category: Quantum Physics

Fully explicit real-valued version of `QPhys.box_level_4`: for a particle of mass `m` in a
one-dimensional infinite square well of width `L`, the energy levels are
`Eₙ = n² π² ℏ² / (2 m L²)` and `E₄ / E₁ = 4²`.
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
("particle in a box") of width `L`:  `Eₙ = n² π² ℏ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- **Infinite-well energy ratio, real-valued form.**  `E₄ / E₁ = 4² = 16`. -/
theorem box_level_4_real (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 4 / boxEnergyReal hbar m L 1 = (4 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  push_cast
  field_simp

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

