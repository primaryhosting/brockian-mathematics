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

/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/
noncomputable def e (x : ZMod 5) : ℂ := om ^ x.val

theorem om_primitive : IsPrimitiveRoot om 5 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem om_pow_five : om ^ 5 = 1 := om_primitive.pow_eq_one

theorem om_pow_mod (k : ℕ) : om ^ (k % 5) = om ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k 5]
  rw [pow_add, pow_mul, om_pow_five, one_pow, one_mul]

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_add (x y : ZMod 5) : e (x + y) = e x * e y := by
  simp only [e, ZMod.val_add, ← pow_add, om_pow_mod]

/-- Orthogonality of the character `e`: summing `e (b * a)` over `a` gives `5` when `b = 0`
and `0` otherwise. -/
theorem sum_e_mul (b : ZMod 5) :
    ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hb : b = 0
  · subst hb
    simp [e_zero, ZMod.card]
  · have hsum : ∑ a : ZMod 5, e a = 0 := by
      have h : ∑ i ∈ Finset.range 5, om ^ i = 0 := om_primitive.geom_sum_eq_zero (by norm_num)
      simp [Finset.sum_range_succ] at h
      show ∑ a : Fin 5, e a = 0
      rw [Fin.sum_univ_five]
      simp only [e, show ((1 : ZMod 5)).val = 1 from rfl, show ((2 : ZMod 5)).val = 2 from rfl,
        show ((3 : ZMod 5)).val = 3 from rfl, show ((4 : ZMod 5)).val = 4 from rfl,
        show ((0 : ZMod 5)).val = 0 from rfl]
      linear_combination h
    have hre := Fintype.sum_equiv (Equiv.mulLeft₀ b hb) (fun a : ZMod 5 => e (b * a)) e
      (fun a => rfl)
    rw [hre, hsum, if_neg hb]

/-- The indicator function of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Spectral decomposition of the ray indicator as a character sum. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  have hcomm : ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r))
      = ∑ a : ZMod 5, e (((n : ZMod 5) - r) * a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  rw [hcomm, sum_e_mul, rayIndicator]
  by_cases h : (n : ZMod 5) = r <;> simp [h, sub_eq_zero]

end Brockian.Characters5

