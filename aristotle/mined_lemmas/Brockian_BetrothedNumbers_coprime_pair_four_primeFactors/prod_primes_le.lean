import Mathlib
/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n` such that
the sum of the divisors of each equals `m + n + 1`, i.e. each is the sum of the *nontrivial*
divisors (excluding `1` and the number itself) of the other. -/

lemma prod_primes_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, ((p : ℚ) / ((p : ℚ) - 1)) ≤ 15 / 4 := by
  have h : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases h with h | h | h | h
  · rw [Finset.card_eq_zero] at h; subst h; norm_num
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have := (g_bounds (hS a (by simp))).2.1
    simp only [Finset.prod_singleton]
    linarith
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have ha := g_bounds (hS a (by simp))
    have hb := g_bounds (hS b (by simp))
    rw [Finset.prod_insert (by simpa using hab), Finset.prod_singleton]
    rcases eq_or_ne a 2 with rfl | ha'
    · nlinarith [ha.2.1, hb.2.2.1 (Ne.symm hab), ha.1, hb.1]
    · nlinarith [ha.2.2.1 ha', hb.2.1, ha.1, hb.1]
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simpa using hbc),
      Finset.prod_singleton, ← mul_assoc]
    exact three_primes_prod_le (hS a (by simp)) (hS b (by simp)) (hS c (by simp)) hab hac hbc

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed (quasi-amicable)
numbers, then `m * n` has at least four distinct prime factors.

The proof: by multiplicativity of `σ` on coprime arguments,
`σ(mn) = σ(m)σ(n) = (m+n+1)^2 > (m+n)^2 ≥ 4mn`, so the abundancy `σ(mn)/(mn)` exceeds `4`.
On the other hand, if `mn` had at most three distinct prime factors then
`σ(mn)/(mn) ≤ ∏_{p ∣ mn} p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4 < 4`, a contradiction. -/
