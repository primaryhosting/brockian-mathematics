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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma prod_le_four_mul_prod_pred {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, p ≤ 4 * ∏ p ∈ S, (p - 1) := by
  have h : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases h with h | h | h | h
  · rw [Finset.card_eq_zero] at h; subst h; simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    simp only [Finset.prod_singleton]
    have := (hS a (by simp)).two_le
    omega
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    exact two_bound_sym (hS a (by simp)) (hS b (by simp)) hab
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have ha := hS a (by simp)
    have hb := hS b (by simp)
    have hc := hS c (by simp)
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
      Finset.prod_singleton, Finset.prod_insert (by simp [hab, hac]),
      Finset.prod_insert (by simp [hbc]), Finset.prod_singleton]
    calc a * (b * c) = a * b * c := by ring
      _ ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := three_bound_sym ha hb hc hab hac hbc
      _ = 4 * ((a - 1) * ((b - 1) * (c - 1))) := by ring

/-- A number with at most three distinct prime factors is not `4`-abundant. -/
