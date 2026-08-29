import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

theorem odd_zumkeller_not_square {n : ℕ} (hodd : Odd n) (h : Zumkeller n) : ¬ IsSquare n := by
  intro hsq
  obtain ⟨S, _, hsum⟩ := h
  have hn : n ≠ 0 := by rintro rfl; simp at hodd
  have h1 : (∑ d ∈ n.divisors, d) % 2 = 0 := by omega
  have h2 := sum_divisors_mod_two hodd
  have h3 := Nat.odd_iff.mp (odd_card_divisors_of_isSquare hn hsq)
  omega

end Brockian.ZumkellerNumbers

