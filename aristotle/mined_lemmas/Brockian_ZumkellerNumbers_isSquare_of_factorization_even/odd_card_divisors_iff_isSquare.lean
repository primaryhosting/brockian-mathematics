import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset


lemma odd_card_divisors_iff_isSquare {t : ℕ} (ht : t ≠ 0) :
    Odd t.divisors.card ↔ IsSquare t := by
  rw [Nat.card_divisors ht]
  constructor
  · intro h
    refine isSquare_of_factorization_even ht ?_
    intro p
    by_cases hp : p ∈ t.primeFactors
    · have h2 : ¬ (2 ∣ ∏ x ∈ t.primeFactors, (t.factorization x + 1)) := by
        simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using h
      have : ¬ (2 ∣ (t.factorization p + 1)) :=
        fun hd => h2 (hd.trans (Finset.dvd_prod_of_mem _ hp))
      rcases Nat.even_or_odd (t.factorization p) with he | ho
      · exact he
      · obtain ⟨c, hc⟩ := ho
        exact absurd ⟨c + 1, by omega⟩ this
    · have hz : t.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
      simp [hz]
  · intro h
    have hev : ∀ p, Even (t.factorization p) := factorization_even_of_isSquare h
    rw [Nat.odd_iff, ← Nat.not_even_iff, even_iff_two_dvd]
    intro hdvd
    obtain ⟨p, hp, hpd⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff _).1 hdvd
    obtain ⟨c, hc⟩ := hev p
    omega

/-- The odd divisors of `n = 2 ^ k * t` (with `t` odd) are exactly the divisors of `t`. -/
