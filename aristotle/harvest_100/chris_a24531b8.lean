/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` associated to `ω`. -/
noncomputable def e (a : ZMod 5) : ℂ := ω ^ a.val

/-- `ω` is a primitive fifth root of unity. -/
theorem isPrimitiveRoot_ω : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  norm_num at h
  exact h

theorem ω_pow_five : ω ^ 5 = 1 := isPrimitiveRoot_ω.pow_eq_one

/-- The five powers of `ω` sum to zero. -/
theorem geom_sum_ω : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h := isPrimitiveRoot_ω.geom_sum_eq_zero (by norm_num)
  simp [Finset.sum_range_succ] at h
  linear_combination h

theorem e_zero : e 0 = 1 := by simp [e]

/-- Sum of the character over all of `ZMod 5` vanishes. -/
theorem sum_e : ∑ a : ZMod 5, e a = 0 := by
  show ∑ a : Fin 5, e a = 0
  rw [Fin.sum_univ_five]
  have : ∀ k : Fin 5, e k = ω ^ (k : ℕ) := fun k => rfl
  simp only [this]
  norm_num
  linear_combination geom_sum_ω

/-- Orthogonality relation for the character `e`. -/
theorem sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [e_zero]
  · rw [if_neg hb]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h : ∑ a : ZMod 5, e (b * a) = ∑ a : ZMod 5, e a :=
      Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ (fun a => rfl)
    rw [h, sum_e]

/-- The indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Indicator decomposition: the ray indicator `𝟙[n ≡ r (mod 5)]` equals
`(1/5) Σ_{a : ZMod 5} e (a * (n - r))`. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hb
  have hcomm : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  rw [hcomm, sum_e_mul, rayIndicator]
  by_cases h : (n : ZMod 5) = r
  · have hb0 : b = 0 := by rw [hb, sub_eq_zero]; exact h
    rw [if_pos h, if_pos hb0]
    norm_num
  · have hb0 : b ≠ 0 := sub_ne_zero_of_ne h
    rw [if_neg h, if_neg hb0]
    norm_num

end Characters5
end Brockian

