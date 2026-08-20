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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `a ↦ ω ^ a.val` on `ZMod 5`. -/
noncomputable def e (a : ZMod 5) : ℂ := ω ^ a.val

lemma omega_pow_five : ω ^ 5 = 1 := by
  rw [ω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  exact ⟨1, by push_cast; ring⟩

lemma omega_ne_one : ω ≠ 1 := by
  rw [ω, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  field_simp at hn
  have h5 : (1 : ℂ) = 5 * n := by linear_combination hn
  have hz : (1 : ℤ) = 5 * n := by exact_mod_cast h5
  omega

lemma sum_omega_pow : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = ω ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) omega_ne_one
  · exact h1

/-- Orthogonality for the character `e`: `∑ a, e (b * a) = 5` if `b = 0`, and `0` otherwise. -/
lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hb : b = 0
  · subst hb
    simp only [zero_mul, e]
    norm_num
  · rw [if_neg hb]
    have h : ∑ a : ZMod 5, e (b * a) = ∑ a : ZMod 5, e a :=
      Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ (fun _ => rfl)
    rw [h]
    show (∑ a : Fin 5, ω ^ (a : ℕ)) = 0
    rw [Fin.sum_univ_five]
    norm_num
    linear_combination sum_omega_pow

/-- The indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Indicator decomposition: the ray indicator `𝟙[n ≡ r (mod 5)]` equals
`(1/5) ∑_{a : ZMod 5} e (a * (n - r))`, spectrally decomposing membership in one ray of the
five-ray wheel. -/
theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hb
  have hcomm : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) :=
    Finset.sum_congr rfl fun a _ => by rw [mul_comm]
  rw [hcomm, sum_e_mul, rayIndicator]
  by_cases h : (n : ZMod 5) = r
  · have hb0 : b = 0 := by rw [hb, sub_eq_zero]; exact h
    simp [h, hb0]
  · have hb0 : b ≠ 0 := by rw [hb, Ne, sub_eq_zero]; exact h
    simp [h, hb0]

end Brockian.Characters5
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

