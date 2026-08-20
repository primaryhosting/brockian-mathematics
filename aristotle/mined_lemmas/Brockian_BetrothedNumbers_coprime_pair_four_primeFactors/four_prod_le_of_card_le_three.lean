/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `σ₁ n` is the sum of divisors of `n`. -/

lemma four_prod_le_of_card_le_three (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    4 * ∏ p ∈ S, p ≤ 15 * ∏ p ∈ S, (p - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha : (2 : ℕ) ≤ a := (hS a (by simp)).two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have hpa := hS a (by simp)
    have hpb := hS b (by simp)
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact four_prod_le_two a b hpa hlt
    · have := four_prod_le_two b a hpb hlt
      linarith
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have hpa := hS a (by simp)
    have hpb := hS b (by simp)
    have hpc := hS c (by simp)
    have hprod : ∀ f : ℕ → ℕ, ∏ p ∈ ({a, b, c} : Finset ℕ), f p = f a * (f b * f c) := by
      intro f
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton]
    rw [hprod (fun p => p), hprod (fun p => p - 1)]
    rcases lt_trichotomy a b with h1 | h1 | h1
    · rcases lt_trichotomy b c with h2 | h2 | h2
      · have := four_prod_le_three a b c hpa hpc h1 h2
        linarith [this]
      · exact absurd h2 hbc
      · rcases lt_trichotomy a c with h3 | h3 | h3
        · have := four_prod_le_three a c b hpa hpb h3 h2
          linarith [this]
        · exact absurd h3 hac
        · have := four_prod_le_three c a b hpc hpb h3 h1
          linarith [this]
    · exact absurd h1 hab
    · rcases lt_trichotomy a c with h2 | h2 | h2
      · have := four_prod_le_three b a c hpb hpc h1 h2
        linarith [this]
      · exact absurd h2 hac
      · rcases lt_trichotomy b c with h3 | h3 | h3
        · have := four_prod_le_three b c a hpb hpa h3 h2
          linarith [this]
        · exact absurd h3 hbc
        · have := four_prod_le_three c b a hpc hpa h3 h1
          linarith [this]

/-- Any positive integer whose set of prime factors has at most three elements satisfies
`4 * σ₁ N ≤ 15 * N`, in particular its abundancy index is at most `15/4 < 4`. -/
