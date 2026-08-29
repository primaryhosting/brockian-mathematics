import Mathlib

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

/-
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
two distinct positive integers each of whose sum of *proper* divisors is one more
than the other, i.e. `σ m = σ n = m + n + 1`. -/

theorem odd_sigma_iff {n : ℕ} (hn : n ≠ 0) :
    Odd (sigma 1 n) ↔ ∃ a, n = a ^ 2 ∨ n = 2 * a ^ 2 := by
  rw [sq_or_two_mul_sq_iff hn, sigma_one_apply, Nat.sum_divisors hn]
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd,
    Prime.dvd_finset_prod_iff Nat.prime_two.prime]
  constructor
  · intro h p hp
    by_cases hmem : p ∈ n.primeFactors
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      by_contra hodd
      refine h ⟨p, hmem, ?_⟩
      have hns : ¬ Odd (∑ i ∈ range (n.factorization p + 1), p ^ i) := by
        rw [odd_geomSum_iff hpp]
        push_neg
        exact ⟨hp, hodd⟩
      rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hns
      exact hns
    · have hz : n.factorization p = 0 := by
        rw [← Nat.support_factorization] at hmem
        exact Finsupp.notMem_support_iff.mp hmem
      simp [hz]
  · rintro h ⟨p, hmem, hdvd⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmem
    have hodd : Odd (∑ i ∈ range (n.factorization p + 1), p ^ i) := by
      rw [odd_geomSum_iff hpp]
      rcases eq_or_ne p 2 with rfl | hp2
      · exact Or.inl rfl
      · exact Or.inr (h p hp2)
    rw [Nat.odd_iff] at hodd
    omega

/-! ### The reduction -/

/-- For a betrothed pair, having equal parity is equivalent to both members being
a square or twice a square. -/
