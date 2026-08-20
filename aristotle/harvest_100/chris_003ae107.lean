import Mathlib

/-!
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`, `e x = ω ^ x`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

/-- The number of elements of `S` lying on the ray `r` mod `5`.
(The binder type `n : ℕ` is stated explicitly so that the predicate is the intended
congruence condition on the elements of `S`.) -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => (n : ZMod 5) = r).card

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5)
      = 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have key : ((5 * n : ℤ) : ℂ) = 1 := by
    have h3 : ((5 * n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = 1 * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      linear_combination (-5 : ℂ) * hn
    exact mul_right_cancel₀ h2 h3
  have h5 : (5 : ℤ) * n = 1 := by exact_mod_cast key
  omega

lemma e_zero : e 0 = 1 := by simp [e]

lemma sum_e_univ : ∑ a : ZMod 5, e a = 0 := by
  have hrange : ∑ a : ZMod 5, e a = ∑ k ∈ Finset.range 5, omega ^ k := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    show ∑ a : Fin 5, e a = _
    rw [Fin.sum_univ_five]
    norm_num [e, ZMod.val]
  rw [hrange, geom_sum_eq omega_ne_one 5, omega_pow_five, sub_self, zero_div]

/-- Orthogonality: summing `e (a * x)` over all `a : ZMod 5` gives `5` if `x = 0` and `0`
otherwise. -/
lemma sum_e_mul (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then 5 else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [e_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hx,
      Fintype.sum_equiv (Equiv.mulRight₀ x hx) (fun a => e (a * x)) e (fun a => rfl),
      sum_e_univ]

/-- The indicator function of the ray `r`, written as a character sum. -/
lemma rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  rw [sum_e_mul]
  by_cases h : (n : ZMod 5) = r
  · rw [if_pos h, if_pos (by rw [h, sub_self])]
    norm_num
  · rw [if_neg h, if_neg (by simpa [sub_eq_zero] using h), mul_zero]

/-- Ray-count identity: the number of elements of `S` on the ray `r` mod `5` equals
`(1/5) Σ_a Σ_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have h1 : ((raySum S r : ℕ) : ℂ)
      = ∑ n ∈ S, (if (n : ZMod 5) = r then (1 : ℂ) else 0) := by
    simp [raySum, Finset.sum_boole]
  rw [h1]
  simp_rw [rayIndicator_eq_charSum]
  rw [← Finset.mul_sum, Finset.sum_comm]

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

