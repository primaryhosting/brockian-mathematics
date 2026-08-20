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

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite potential well ("particle in a box") of width `L`,
with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_div_boxEnergy_one {hbar m L : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hL : 0 < L)
    (n : ℕ) : boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have h1 : boxEnergy hbar m L 1 ≠ 0 := boxEnergy_one_ne_zero hh hm hL
  have hEn : boxEnergy hbar m L n = (n : ℝ) ^ 2 * boxEnergy hbar m L 1 := by
    unfold boxEnergy
    push_cast
    ring
  rw [hEn, mul_div_assoc, div_self h1, mul_one]

/-- **Box Level 1.** The infinite-well energy ratio `E₁ / E₁` equals `1² = 1`.
Since `Eₙ = n² E₁`, the ratio of the first level to itself is `1²`. -/
