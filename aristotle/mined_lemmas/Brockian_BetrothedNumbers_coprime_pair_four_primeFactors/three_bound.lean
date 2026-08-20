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

lemma three_bound {a b c : ℕ} (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 5 ≤ c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 2 + x := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 3 + y := ⟨b - 3, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, c = 5 + z := ⟨c - 5, by omega⟩
  simp only [show 2 + x - 1 = 1 + x by omega, show 3 + y - 1 = 2 + y by omega,
    show 5 + z - 1 = 4 + z by omega]
  have h : 4 * ((1 + x) * (2 + y) * (4 + z)) =
      (2 + x) * (3 + y) * (5 + z) +
        (2 + 6 * y + 17 * x + 11 * (x * y) + 2 * z + 2 * (y * z) + 5 * (x * z) +
          3 * (x * y * z)) := by ring
  omega

/-- A prime larger than another prime is at least `3`. -/
