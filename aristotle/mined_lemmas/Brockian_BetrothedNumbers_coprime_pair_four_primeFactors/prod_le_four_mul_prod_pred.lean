import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `Betrothed m n` says that `m` and `n` are *betrothed* (quasi-amicable) numbers:
both are positive and each one's sum of divisors equals `m + n + 1`. -/

lemma prod_le_four_mul_prod_pred {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (h3 : P.card ≤ 3) :
    ∏ p ∈ P, p ≤ 4 * ∏ p ∈ P, (p - 1) := by
  rcases lt_or_ge P.card 3 with hlt | hge
  · -- crude bound `p ≤ 2 * (p - 1)`, giving `∏ p ≤ 2 ^ card * ∏ (p - 1) ≤ 4 * ∏ (p - 1)`
    have hstep : ∏ p ∈ P, p ≤ ∏ p ∈ P, (2 * (p - 1)) := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      have := (hP p hp).two_le
      omega
    have hsplit : ∏ p ∈ P, (2 * (p - 1)) = 2 ^ P.card * ∏ p ∈ P, (p - 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hpow : (2:ℕ) ^ P.card ≤ 4 := by
      calc (2:ℕ) ^ P.card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    calc ∏ p ∈ P, p ≤ 2 ^ P.card * ∏ p ∈ P, (p - 1) := by rw [← hsplit]; exact hstep
      _ ≤ 4 * ∏ p ∈ P, (p - 1) := Nat.mul_le_mul_right _ hpow
  · have hc : P.card = 3 := le_antisymm h3 hge
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc
    have ha : a.Prime := hP a (by simp)
    have hb : b.Prime := hP b (by simp)
    have hcp : c.Prime := hP c (by simp)
    have h1 : ∏ p ∈ ({a, b, c} : Finset ℕ), p = a * b * c := by
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton, ← mul_assoc]
    have h2 : ∏ p ∈ ({a, b, c} : Finset ℕ), (p - 1) = (a - 1) * ((b - 1) * (c - 1)) := by
      rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
        Finset.prod_singleton]
    rw [h1, h2, ← mul_assoc (a - 1) (b - 1) (c - 1)]
    exact three_primes_distinct ha hb hcp hab hac hbc

/-- If `σ(N) > 4N` then `N` has at least four distinct prime factors. -/
