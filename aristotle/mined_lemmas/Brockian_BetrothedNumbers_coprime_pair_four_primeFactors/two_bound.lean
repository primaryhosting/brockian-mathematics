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

lemma two_bound {a b : ℕ} (ha : 2 ≤ a) (hb : 3 ≤ b) : a * b ≤ 4 * ((a - 1) * (b - 1)) := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 2 + x := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 3 + y := ⟨b - 3, by omega⟩
  simp only [show 2 + x - 1 = 1 + x by omega, show 3 + y - 1 = 2 + y by omega]
  have h : 4 * ((1 + x) * (2 + y)) = (2 + x) * (3 + y) + (2 + 2 * y + 5 * x + 3 * (x * y)) := by
    ring
  omega

/-- Three distinct primes: `a * b * c ≤ 4 * ((a-1)*(b-1)*(c-1))`, given `2 ≤ a`, `3 ≤ b`, `5 ≤ c`. -/
