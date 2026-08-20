import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyiPush_crit (m n : ℕ) (z : ℂ)
    (hz : aeval z (derivative (belyiPush (m + 1) (n + 1))) = 0) :
    aeval z (belyiPush (m + 1) (n + 1)) ∈ ({0, 1} : Set ℂ) := by
  have hcC : ((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1)) /
      (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)) : ℚ) : ℂ) ≠ 0 := by
    have hc : (((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1)) ≠ 0 := by positivity
    exact_mod_cast hc
  rw [belyiPush_eq, derivative_C_mul, derivative_pow_mul_one_sub_pow] at hz
  simp only [map_mul, map_sub, aeval_C, aeval_X, map_pow, map_one] at hz
  have hz3 : z = ((0 : ℚ) : ℂ) ∨ z = ((1 : ℚ) : ℂ) ∨
      z = ((((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2) : ℚ) : ℂ) := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (by simpa using h) hcC
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with hz0 | hz1
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at hz0
        · left
          have := (pow_eq_zero_iff (n := m) (a := z) hm.ne').mp hz0
          simpa using this
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp at hz1
        · right; left
          have h' := (pow_eq_zero_iff (n := n) (a := (1 - z)) hn.ne').mp hz1
          have : z = 1 := by linear_combination -h'
          simpa using this
    · right; right
      have hne : ((m : ℂ) + (n : ℂ) + 2) ≠ 0 := by
        have : ((m : ℚ) + (n : ℚ) + 2) ≠ 0 := by positivity
        exact_mod_cast this
      simp only [map_add, map_one, map_natCast, map_ofNat] at h2
      push_cast
      rw [eq_div_iff hne]
      linear_combination -h2
  rcases hz3 with h | h | h <;> rw [h, aeval_rat]
  · left; rw [belyiPush_eval_zero]; simp
  · left; rw [belyiPush_eval_one]; simp
  · right; rw [belyiPush_eval_ratio]; simp

