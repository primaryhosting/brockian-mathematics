/-!
# Box Level 6
Category: Quantum Physics
Target: QPhys.box_level_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires every `import` command to precede any other
syntax in a file, so the mandated module docstring above forces this file to be
import-free (only the implicit `Init` prelude is available).  The statement below
is therefore phrased with the natural-number energy scale `e1` standing for the
ground-state energy `π²ħ²/(2mL²)` of the one-dimensional infinite square well.
The companion file `RequestProject/QPhysReal.lean` develops the same result for
the genuine real-valued formula `Eₙ = n²π²ħ²/(2mL²)` using Mathlib.
-/

namespace QPhys

/-- Energy levels of a particle in a one-dimensional infinite square well
("particle in a box"), expressed in units of the ground-state energy
`e1 = π²ħ²/(2mL²)`: the `n`-th level is `Eₙ = n² · e1`. -/
def boxEnergy (e1 : Nat) (n : Nat) : Nat := n ^ 2 * e1

/-- The sixth level of the infinite well is `6²` times the ground state. -/
theorem boxEnergy_six (e1 : Nat) : boxEnergy e1 6 = 6 ^ 2 * boxEnergy e1 1 := by
  unfold boxEnergy
  simp

/-- The infinite-well energy ratio: `E₆ / E₁ = 6²`. -/
theorem box_level_6 (e1 : Nat) (h : 0 < e1) :
    boxEnergy e1 6 / boxEnergy e1 1 = 6 ^ 2 := by
  unfold boxEnergy
  simp [Nat.mul_div_cancel _ h]

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
# Box Level 6 (real-valued version)

The infinite square well energy levels `Eₙ = n² π² ħ² / (2 m L²)` and the ratio
`E₆ / E₁ = 6²`.
-/

namespace QPhys

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional
infinite square well of width `L`: `Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the one-dimensional infinite square well, `E₆ / E₁ = 6² = 36`. -/
theorem box_level_6_real (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 6 / boxEnergyReal hbar m L 1 = (6 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  field_simp
  ring

end QPhys

