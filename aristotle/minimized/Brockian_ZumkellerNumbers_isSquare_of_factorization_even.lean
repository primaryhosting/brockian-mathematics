import Mathlib

namespace Brockian.ZumkellerNumbers

open Finset

lemma isSquare_of_factorization_even {t : ℕ} (ht : t ≠ 0)
    (h : ∀ p, Even (t.factorization p)) : IsSquare t := by
  have key : ∏ p ∈ t.primeFactors, p ^ t.factorization p = t := by
    simpa [Nat.support_factorization, Finsupp.prod] using Nat.factorization_prod_pow_eq_self ht
  refine ⟨∏ p ∈ t.primeFactors, p ^ (t.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← key]
  refine Finset.prod_congr rfl ?_
  intro p _
  rw [← pow_add]
  congr 1
  obtain ⟨c, hc⟩ := h p
  omega

/-- Every prime exponent in the factorization of a square is even. -/
