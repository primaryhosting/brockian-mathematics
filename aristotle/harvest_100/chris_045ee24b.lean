/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires every `import` command to appear before any other
syntax in a file, so this file — whose first token must be the header comment
above — is written without imports.  It therefore uses only the Lean core
library, in particular the core field class `Lean.Grind.Field`, which the real
numbers of Mathlib instantiate.  The Mathlib specialisation to `ℝ` with the
genuine constant `Real.pi` is in `RequestProject/BoxLevel7Real.lean`.
-/

namespace QPhys

open Lean.Grind

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant
`hbar` and circle constant `pi`:

`E n = n² π² ħ² / (2 m L²)`.

The level index `n` is taken in the ambient field `K`; the physical levels are
the values at `n = 1, 2, 3, …`. -/
def boxEnergy {K : Type u} [Field K] (hbar m L pi n : K) : K :=
  n ^ 2 * pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- Every level of the infinite well is `n²` times the ground state energy. -/
theorem boxEnergy_eq_sq_mul_ground {K : Type u} [Field K] (hbar m L pi n : K) :
    boxEnergy hbar m L pi n = n ^ 2 * boxEnergy hbar m L pi 1 := by
  unfold boxEnergy
  grind

/-- The ground state energy is nonzero as soon as `2`, `ħ`, `m`, `L` and `π`
are all nonzero. -/
theorem boxEnergy_one_ne_zero {K : Type u} [Field K] (hbar m L pi : K)
    (h2 : (2 : K) ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) (hpi : pi ≠ 0) :
    boxEnergy hbar m L pi 1 ≠ 0 := by
  unfold boxEnergy
  grind

/-- **Box level 7.**  For a particle in a one-dimensional infinite potential
well, the ratio of the seventh energy level to the ground state energy is
`7² = 49`. -/
theorem box_level_7 {K : Type u} [Field K] (hbar m L pi : K)
    (h2 : (2 : K) ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) (hpi : pi ≠ 0) :
    boxEnergy hbar m L pi 7 / boxEnergy hbar m L pi 1 = 7 ^ 2 := by
  unfold boxEnergy
  grind

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
import RequestProject.BoxLevel7

/-!
# Box Level 7 over the real numbers

Specialisation of `QPhys.box_level_7` to the field `ℝ` with the genuine
circle constant `Real.pi`.
-/

namespace QPhys

/-- The energy levels of the one-dimensional infinite well, as real numbers:
`Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  boxEnergy hbar m L Real.pi (n : ℝ)

theorem boxEnergyReal_eq (hbar m L : ℝ) (n : ℕ) :
    boxEnergyReal hbar m L n = (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2) :=
  rfl

/-- **Box level 7 over `ℝ`.**  For a particle of nonzero mass `m` in a
one-dimensional infinite well of nonzero width `L`, with nonzero reduced Planck
constant `ħ`, the ratio of the seventh energy level to the ground state energy
is `7² = 49`. -/
theorem box_level_7_real {hbar m L : ℝ} (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 7 / boxEnergyReal hbar m L 1 = 7 ^ 2 := by
  have h : boxEnergyReal hbar m L 7 / boxEnergyReal hbar m L 1
      = boxEnergy hbar m L Real.pi 7 / boxEnergy hbar m L Real.pi 1 := by
    unfold boxEnergyReal
    norm_num
  rw [h]
  exact box_level_7 hbar m L Real.pi (by norm_num) hhbar hm hL Real.pi_ne_zero

end QPhys

