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

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` are *betrothed* (quasi-amicable) numbers: they are distinct and each one's
sum of divisors equals `m + n + 1`. -/

lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  have key : ∀ p ∈ n.primeFactors, p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2)
      = p ^ (n.factorization p) := by
    intro p _
    rw [← pow_add]
    congr 1
    obtain ⟨c, hc⟩ := h p
    omega
  rw [Finset.prod_congr rfl key]
  exact (Nat.factorization_prod_pow_eq_self hn).symm.trans
    (Nat.prod_factorization_eq_prod_primeFactors _)

/-- For an odd number, an odd sum of divisors forces the number to be a square. -/
