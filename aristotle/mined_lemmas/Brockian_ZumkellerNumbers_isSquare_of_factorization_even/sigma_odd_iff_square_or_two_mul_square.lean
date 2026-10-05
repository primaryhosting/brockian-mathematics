import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset


theorem sigma_odd_iff_square_or_two_mul_square (n : ℕ) (hn : 0 < n) :
    Odd (∑ d ∈ n.divisors, d) ↔ (IsSquare n ∨ IsSquare (2 * n)) := by
  obtain ⟨k, t, hto, hkt⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hn0 : n ≠ 0 := hn.ne'
  have ht : t ≠ 0 := by rintro rfl; simp at hkt; exact hn0 hkt
  have hstep : Odd (∑ d ∈ n.divisors, d) ↔ IsSquare t := by
    rw [Finset.odd_sum_iff_odd_card_odd (fun d => d), filter_odd_divisors hn0 hkt hto,
      odd_card_divisors_iff_isSquare ht]
  rw [hstep]
  have ht2 : t.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using hto)
  have hfac : ∀ p, p ≠ 2 → n.factorization p = t.factorization p := by
    intro p hp
    rw [hkt, Nat.factorization_mul (by positivity) ht]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Ne.symm hp]
  constructor
  · intro hsq
    obtain ⟨m, hm⟩ := hsq
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      exact ⟨2 ^ j * m, by rw [hkt, hm, hj]; ring⟩
    · right
      exact ⟨2 ^ (j + 1) * m, by rw [hkt, hm, hj]; ring⟩
  · intro h
    refine isSquare_of_factorization_even ht ?_
    intro p
    by_cases hp2 : p = 2
    · subst hp2; simp [ht2]
    · rw [← hfac p hp2]
      rcases h with h | h
      · exact factorization_even_of_isSquare h p
      · have : (2 * n).factorization p = n.factorization p := by
          rw [Nat.factorization_mul (by norm_num) hn0]
          simp [Nat.Prime.factorization Nat.prime_two, Ne.symm hp2]
        rw [← this]
        exact factorization_even_of_isSquare h p

end Brockian.ZumkellerNumbers

