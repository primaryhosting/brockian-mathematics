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

theorem exists_sq_of_even_factorization {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p, Even (m.factorization p)) : ∃ t, m = t ^ 2 := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  have hself : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m := by
    have := Nat.factorization_prod_pow_eq_self hm
    rwa [Finsupp.prod, Nat.support_factorization] at this
  have key : ∏ p ∈ m.primeFactors, p ^ m.factorization p
      = (∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    obtain ⟨c, hc⟩ := h p
    rw [hc, ← pow_mul]
    congr 1
    omega
  exact hself.symm.trans key

/-- Being a square or twice a square is the same as having even exponent at every odd prime. -/
