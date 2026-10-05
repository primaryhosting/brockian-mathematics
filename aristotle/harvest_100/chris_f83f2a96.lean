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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` sending `x` to `ω ^ x`. -/
noncomputable def e (x : ZMod 5) : ℂ := ω ^ x.val

/-- The number of elements of `S` lying on the ray `r` modulo `5`. -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => (n : ZMod 5) = r).card

theorem omega_pow_five : ω ^ 5 = 1 := by
  rw [ω, ← Complex.exp_nat_mul]
  norm_num
  rw [show (5 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * Real.pi * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

theorem omega_ne_one : ω ≠ 1 := by
  rw [ω, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have h2 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hn
  have : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

/-- The character sum of `e` over all of `ZMod 5` vanishes. -/
theorem sum_e_eq_zero : ∑ a : ZMod 5, e a = 0 := by
  have h : ∑ a : ZMod 5, e a = ∑ a : Fin 5, ω ^ (a : ℕ) := rfl
  rw [h, Fin.sum_univ_five]
  have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  have hprod : (ω - 1) * (ω ^ 0 + ω ^ 1 + ω ^ 2 + ω ^ 3 + ω ^ 4) = 0 := by
    have : (ω - 1) * (ω ^ 0 + ω ^ 1 + ω ^ 2 + ω ^ 3 + ω ^ 4) = ω ^ 5 - 1 := by ring
    rw [this, omega_pow_five, sub_self]
  have := (mul_eq_zero.mp hprod).resolve_left hne
  simpa using this

/-- Orthogonality: the character sum over `a : ZMod 5` of `e (a * x)`. -/
theorem sum_e_mul (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then (5 : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [e, ZMod.val_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hx]
    have : ∑ a : ZMod 5, e (a * x) = ∑ a : ZMod 5, e a :=
      Fintype.sum_equiv (Equiv.mulRight₀ x hx) _ _ (fun a => rfl)
    rw [this, sum_e_eq_zero]

/-- The indicator of the ray `x = 0` as a character sum. -/
theorem rayIndicator_eq_charSum (x : ZMod 5) :
    (if x = 0 then (1 : ℂ) else 0) = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * x) := by
  rw [sum_e_mul]
  by_cases hx : x = 0 <;> simp [hx]

/-- Ray-count identity: the number of elements of `S` on the ray `r` equals
`(1/5) ∑_{a} ∑_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have hcard : ((raySum S r : ℕ) : ℂ) = ∑ n ∈ S, if (n : ZMod 5) = r then (1 : ℂ) else 0 := by
    rw [raySum, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => by by_cases h : (n : ZMod 5) = r <;> simp [h])
  rw [hcard, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hiff : ((n : ZMod 5) = r) ↔ ((n : ZMod 5) - r = 0) := (sub_eq_zero).symm
  rw [show (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (if (n : ZMod 5) - r = 0 then (1 : ℂ) else 0) by
    by_cases h : (n : ZMod 5) = r
    · simp [h]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]]
  exact rayIndicator_eq_charSum _

end Characters5
end Brockian

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

