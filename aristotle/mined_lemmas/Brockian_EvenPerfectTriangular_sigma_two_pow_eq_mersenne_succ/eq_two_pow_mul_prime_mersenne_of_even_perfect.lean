import Mathlib

namespace Brockian.EvenPerfectTriangular

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number. -/

theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ}
    (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_not_even hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne,
    add_mul, one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd
      (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h₁ =>
      have j1 : j = 1 := Eq.trans hj.symm h₁
      rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h₁
      simp [h₁, j1]
  | inr h₁ =>
      have jcon := Eq.trans hj.symm h₁
      rw [← one_mul j, ← mul_assoc, mul_one] at jcon
      have hj0 : j ≠ 0 := by
        intro hjzero
        subst j
        simp at hpos
      have jcon2 := mul_right_cancel₀ hj0 jcon
      exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)

/-- Every even perfect number is a triangular number. -/
