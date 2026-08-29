import Mathlib

/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
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

/-- The `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`, up to normalization:
`ψ_n(x) = sin (n π x / L)`.  It vanishes at both walls `x = 0` and `x = L`. -/

theorem boxEnergy_ratio (hbar m L : ℝ) (hbar0 : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) (n : ℕ) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [boxEnergy]
  rw [div_div_div_cancel_right₀]
  · field_simp
    norm_num
  · exact mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero 2 hL)

end QPhys

