import Mathlib

namespace Brockian.OddPerfectThreePrimes

open Finset

/-- A geometric-sum identity: `(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/

lemma odd_deficient_of_primeFactors_card_le_two {n : ℕ} (ho : Odd n)
    (hc : n.primeFactors.card ≤ 2) : Nat.Deficient n := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  interval_cases h : n.primeFactors.card
  · have : n = 1 := by
      have := Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp h)
      tauto
    simpa [this] using Nat.deficient_one
  · have : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr h
    exact this.deficient
  · obtain ⟨p, q, hpq, hS⟩ := Finset.card_eq_two.mp h
    exact odd_deficient_of_primeFactors_eq_pair ho hpq hS

/-- An odd perfect number has at least three distinct prime factors. -/
