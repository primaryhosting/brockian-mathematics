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

-- (Lean does not permit a `/-!` module docstring before `import`; the header above is the
-- same text as a plain block comment, and is repeated as a module docstring below.)
import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers each of whose
sum of divisors equals `m + n + 1`. -/

theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    (∃ k, n = k ^ 2) ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨k, rfl⟩ p
    rw [Nat.factorization_pow]
    simp [Nat.two_mul]
  · intro h
    have key : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
      rw [← Nat.support_factorization]
      exact Nat.factorization_prod_pow_eq_self hn
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_pow]
    have hcongr : ∀ p ∈ n.primeFactors,
        (p ^ (n.factorization p / 2)) ^ 2 = p ^ (n.factorization p) := by
      intro p _
      rw [← pow_mul]
      congr 1
      obtain ⟨c, hc⟩ := h p
      omega
    rw [Finset.prod_congr rfl hcongr, key]

/-- A positive natural number is a square or twice a square iff every odd prime occurs to an
even power in its factorization. -/
