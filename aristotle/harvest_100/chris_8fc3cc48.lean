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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

@[inherit_doc] scoped notation "ω" => Brockian.Characters5.omega

/-- The additive character `e : ZMod 5 → ℂ`, `e a = ω ^ a.val`. -/
noncomputable def e (a : ZMod 5) : ℂ := ω ^ (a.val)

lemma omega_pow_five : ω ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have h : ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_two_pi_mul_I]

lemma omega_ne_one : ω ≠ 1 := by
  rw [omega]
  intro hEq
  rw [Complex.exp_eq_one_iff] at hEq
  obtain ⟨n, hn⟩ := hEq
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h : ((1 : ℂ) / 5) * (2 * (Real.pi : ℂ) * Complex.I)
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hn
  have hn5 : (n : ℂ) = 1 / 5 := (mul_right_cancel₀ hc h).symm
  have h2 : ((5 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast [hn5]; ring
  have h3 := (Int.cast_injective (α := ℂ)) h2
  omega

lemma sum_omega_pow : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have hfac : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = ω ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at hfac
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  have hsum : ∀ f : ZMod 5 → ℂ, ∑ a : ZMod 5, f a = f 0 + f 1 + f 2 + f 3 + f 4 := by
    intro f
    show ∑ a : Fin 5, f a = _
    rw [Fin.sum_univ_five]
  have hcase : ∀ c : ZMod 5, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by decide
  have key := sum_omega_pow
  rcases hcase b with h | h | h | h | h <;> subst h <;> rw [hsum] <;>
    norm_num +decide [e, ZMod.val] <;> linear_combination key

/-- The indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Indicator decomposition: the ray indicator `𝟙[n ≡ r (mod 5)]` equals
`(1/5) Σ_{a : ZMod 5} e (a * (n - r))`. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hb
  have hcomm : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) := by
    exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]
  rw [hcomm, sum_e_mul, rayIndicator]
  by_cases h : (n : ZMod 5) = r
  · have hb0 : b = 0 := by rw [hb, h, sub_self]
    simp [h, hb0]
  · have hb0 : b ≠ 0 := fun hc => h (sub_eq_zero.mp hc)
    simp [h, hb0]

end Characters5
end Brockian

