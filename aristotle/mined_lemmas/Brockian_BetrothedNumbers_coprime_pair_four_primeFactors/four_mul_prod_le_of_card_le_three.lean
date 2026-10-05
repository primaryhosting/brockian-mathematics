/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and
the sum of the divisors of each equals `m + n + 1`. -/

lemma four_mul_prod_le_of_card_le_three {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hcard : S.card ≤ 3) :
    4 * ∏ p ∈ S, p ≤ 15 * ∏ p ∈ S, (p - 1) := by
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3) with h | h | h | h
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha : a.Prime := hS a (by simp)
    have ha2 := ha.two_le
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    exact four_mul_prod_two_le' ha hb hab
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have ha : a.Prime := hS a (by simp)
    have hb : b.Prime := hS b (by simp)
    have hc : c.Prime := hS c (by simp)
    have habc := four_mul_prod_three_le' ha hb hc hab hac hbc
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc,
      Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
    calc 4 * (a * (b * c)) = 4 * (a * b * c) := by ring
      _ ≤ 15 * ((a - 1) * (b - 1) * (c - 1)) := habc
      _ = 15 * ((a - 1) * ((b - 1) * (c - 1))) := by ring

/-- If `N` has at most three distinct prime factors then `σ(N) / N ≤ 15 / 4`. -/
