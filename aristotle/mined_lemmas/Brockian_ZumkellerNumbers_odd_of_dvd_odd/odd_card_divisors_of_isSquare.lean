import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

lemma odd_card_divisors_of_isSquare {n : ℕ} (hn : n ≠ 0) (hsq : IsSquare n) :
    Odd n.divisors.card := by
  obtain ⟨k, rfl⟩ := hsq
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.card_divisors hn]
  refine Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one ?_
  intro p _
  have hfac : (k * k).factorization p = 2 * k.factorization p := by
    rw [Nat.factorization_mul hk hk]; simp [two_mul]
  rw [hfac]
  exact ⟨k.factorization p, by ring⟩

/-- An odd Zumkeller number is not a perfect square: being Zumkeller forces `sigma n` to be
even, while for an odd square all divisors are odd and there is an odd number of them, so
`sigma n` would be odd. -/
