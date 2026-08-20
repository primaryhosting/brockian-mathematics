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

set_option grind.warning false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` of `ZMod 5` with values in `ℂ`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := ω ^ x.val

/-- The number of elements of `S` lying on the ray `r` modulo `5`. -/
noncomputable def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => (n : ZMod 5) = r).card

lemma sum_zmod_five (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, f a = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ a : Fin 5, f a = _
  rw [Fin.sum_univ_five]

lemma omega_pow_five : ω ^ 5 = 1 := by
  rw [ω, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : ω ≠ 1 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  intro hc
  have h1 : IsPrimitiveRoot (1 : ℂ) 5 := by
    rw [← hc]; exact (by simpa [ω] using h)
  have := h1.unique IsPrimitiveRoot.one
  norm_num at this

lemma geom_omega : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = ω ^ 5 - 1 := by ring
  rw [omega_pow_five] at h
  have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  have h0 : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = 0 := by rw [h]; ring
  exact (mul_eq_zero.mp h0).resolve_left hne

lemma sum_e_eq_zero : ∑ b : ZMod 5, e b = 0 := by
  rw [sum_zmod_five]
  simp only [e, show (0 : ZMod 5).val = 0 from rfl, show (1 : ZMod 5).val = 1 from rfl,
    show (2 : ZMod 5).val = 2 from rfl, show (3 : ZMod 5).val = 3 from rfl,
    show (4 : ZMod 5).val = 4 from rfl]
  simpa using geom_omega

/-- Orthogonality: the character sum `∑_a e (a * x)` is `5` when `x = 0` and `0` otherwise. -/
lemma sum_char_eq_ite (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hx : x = 0
  · subst hx; simp [e]
  · rw [if_neg hx]
    have h := Equiv.sum_comp (Equiv.mulRight₀ x hx) e
    simpa [sum_e_eq_zero] using h

/-- The indicator of the ray `r` at `n`, expressed as a character sum. -/
lemma rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  by_cases h : (n : ZMod 5) = r
  · rw [sum_char_eq_ite, if_pos h, if_pos (sub_eq_zero.mpr h)]; norm_num
  · rw [sum_char_eq_ite, if_neg h, if_neg (fun hc => h (sub_eq_zero.mp hc))]; simp

/-- Ray-count identity: the number of elements of `S` on ray `r` equals
`(1/5) ∑_{a} ∑_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  have hcard : ((raySum S r : ℕ) : ℂ) = ∑ n ∈ S, if (n : ZMod 5) = r then (1 : ℂ) else 0 := by
    rw [raySum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_eq_charSum n r

end Brockian.Characters5

