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

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- `Betrothed m n` says that `m` and `n` are a pair of *betrothed*
(quasi-amicable) numbers: two distinct positive integers each of whose sum of
divisors equals `m + n + 1`. -/

theorem isSquare_of_even_factorization {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p, Even (m.factorization p)) : ∃ k, m = k ^ 2 := by
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hm]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_mul]
  congr 1
  obtain ⟨c, hc⟩ := h p
  omega

/-- Auxiliary: for odd `p`, the geometric sum `1 + p + ⋯ + p ^ (N-1)` is
congruent to `N` modulo `2`. -/
