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
open scoped Classical

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character on `ZMod 5` sending `a` to `ω ^ a.val`. -/
noncomputable def e (a : ZMod 5) : ℂ := omega ^ a.val

/-- The ray indicator: `1` if `n ≡ r (mod 5)` and `0` otherwise. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * (Real.pi : ℂ) * Complex.I by
    push_cast; ring]
  simpa [mul_comm, mul_assoc, mul_left_comm] using Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hn5 : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  have hgeom : (omega - 1) * ∑ k ∈ Finset.range 5, omega ^ k = omega ^ 5 - 1 := by
    rw [mul_comm]; exact geom_sum_mul omega 5
  have h0 : (omega - 1) * ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
    rw [hgeom, omega_pow_five, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

lemma sum_e : ∑ a : ZMod 5, e a = 0 := by
  have : ∑ a : ZMod 5, e a = ∑ k ∈ Finset.range 5, omega ^ k := by
    rw [Finset.sum_range fun k => omega ^ k]
    rfl
  rw [this, sum_omega_pow]

lemma e_zero : e 0 = 1 := by simp [e]

lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [e_zero, ZMod.card]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg hb]
    have hbij : ∑ a : ZMod 5, e (b * a) = ∑ a : ZMod 5, e a :=
      Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ (fun a => rfl)
    rw [hbij, sum_e]

/-- Indicator decomposition: the ray indicator `𝟙[n ≡ r (mod 5)]` equals
`(1/5) Σ_{a : ZMod 5} e (a * (n - r))`. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hbdef
  have hcomm : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) :=
    Finset.sum_congr rfl fun a _ => by rw [mul_comm]
  rw [hcomm, sum_e_mul]
  by_cases h : b = 0
  · have hnr : (n : ZMod 5) = r := by
      have := sub_eq_zero.mp (hbdef ▸ h)
      exact this
    rw [if_pos h, rayIndicator, if_pos hnr]
    norm_num
  · have hnr : (n : ZMod 5) ≠ r := fun hc => h (by rw [hbdef, hc, sub_self])
    rw [if_neg h, rayIndicator, if_neg hnr]
    norm_num

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

