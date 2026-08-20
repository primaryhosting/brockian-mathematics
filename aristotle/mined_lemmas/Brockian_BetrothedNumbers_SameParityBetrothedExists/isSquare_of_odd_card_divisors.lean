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

import Mathlib
/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the very first command in a file, so the header module
-- docstring above sits immediately after the single `import Mathlib` line.)

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd n.divisors.card) :
    IsSquare n := by
  refine isSquare_of_factorization_even hn fun p => ?_
  by_cases hp : p ∈ n.primeFactors
  · by_contra hev
    rw [Nat.not_even_iff_odd] at hev
    have hdvd : 2 ∣ (n.factorization p + 1) := by obtain ⟨k, hk⟩ := hev; omega
    have h2 : 2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
      hdvd.trans (Finset.dvd_prod_of_mem _ hp)
    rw [← Nat.card_divisors hn] at h2
    rw [Nat.odd_iff] at h
    omega
  · have : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [this]

/-- For odd `m`, the divisor sum has the same parity as the number of divisors. -/
