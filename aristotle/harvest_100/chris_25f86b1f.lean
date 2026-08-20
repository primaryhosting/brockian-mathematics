/-
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-!`,
-- because Lean 4 requires `import` to be the first command in a file.)

import Mathlib

/-!
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
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

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is nonzero for physical parameters
(positive mass, positive width, nonzero `ħ`). -/
theorem boxEnergy_one_ne_zero {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 1 ≠ 0 := by
  unfold boxEnergy
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  positivity

/-- **Box Level 1.** The infinite-well energy ratio `E₁ / E₁ = 1²`. -/
theorem box_level_1 {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 1 / boxEnergy m L hbar 1 = (1 : ℝ) ^ 2 := by
  rw [one_pow]
  exact div_self (boxEnergy_one_ne_zero hm hL hbar0)

/-- The general level ratio: `Eₙ / E₁ = n²`. -/
theorem boxEnergy_ratio {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) (n : ℕ) :
    boxEnergy m L hbar n / boxEnergy m L hbar 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : (2 : ℝ) * m * L ^ 2 ≠ 0 := by positivity
  unfold boxEnergy
  field_simp
  ring

end QPhys

