/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp (2 π i / 5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`: `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

lemma geom_sum_omega : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h := isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ, add_assoc] using h

lemma e_zero : e 0 = 1 := by simp [e, show (0 : ZMod 5).val = 0 from rfl]

/-- The full character sum over `ZMod 5` vanishes. -/
lemma sum_e_eq_zero : ∑ a : ZMod 5, e a = 0 := by
  have hexp : ∀ f : ZMod 5 → ℂ, ∑ a : ZMod 5, f a = f 0 + f 1 + f 2 + f 3 + f 4 :=
    fun f => Fin.sum_univ_five f
  have h1 : e 1 = omega := by simp [e, show (1 : ZMod 5).val = 1 from rfl]
  have h2 : e 2 = omega ^ 2 := by simp [e, show (2 : ZMod 5).val = 2 from rfl]
  have h3 : e 3 = omega ^ 3 := by simp [e, show (3 : ZMod 5).val = 3 from rfl]
  have h4 : e 4 = omega ^ 4 := by simp [e, show (4 : ZMod 5).val = 4 from rfl]
  rw [hexp, e_zero, h1, h2, h3, h4]
  linear_combination geom_sum_omega

/-- Orthogonality of the character `e` on `ZMod 5`. -/
lemma sum_char_eq (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then (5 : ℂ) else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · subst hx
    simp [e_zero]
  · rw [if_neg hx, ← sum_e_eq_zero]
    have hbij : Function.Bijective (fun a : ZMod 5 => a * x) :=
      Finite.injective_iff_bijective.mp (fun _ _ h => mul_right_cancel₀ hx h)
    exact Fintype.sum_bijective (fun a => a * x) hbij _ _ (fun _ => rfl)

/-- The number of elements of `S` lying on the ray `r` modulo `5`. -/
noncomputable def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ :=
  (S.filter fun n : ℕ => (n : ZMod 5) = r).card

/-- Each ray indicator is the average of the characters `e (a * (n - r))`. -/
lemma rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  rw [sum_char_eq]
  by_cases h : (n : ZMod 5) = r
  · simp [h]
  · have h' : (n : ZMod 5) - r ≠ 0 := sub_ne_zero_of_ne h
    simp [h, h']

/-- Ray-count identity: the number of elements of `S` on the ray `r` mod `5` equals
`(1/5) Σ_{a : ZMod 5} Σ_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have h1 : ((raySum S r : ℕ) : ℂ) = ∑ n ∈ S, if (n : ZMod 5) = r then (1 : ℂ) else 0 := by
    rw [raySum]
    exact (Finset.sum_boole (s := S) (p := fun n : ℕ => (n : ZMod 5) = r)).symm
  rw [h1, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_eq_charSum n r

end Characters5
end Brockian

