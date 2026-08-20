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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum of all divisors of `n`, i.e. `σ₁ n`. -/

theorem isKHyperperfect_partner {p : ℕ} (hp : p.Prime) (hq : (partner p).Prime) :
    IsKHyperperfect (p - 1) (p * partner p) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hc1 : c + 2 - 1 = c + 1 := by omega
  have hpartner : partner (c + 2) = c * c + 3 * c + 3 := by
    rw [partner, hc1]; ring
  have hne : c + 2 ≠ partner (c + 2) := by omega
  refine ⟨?_, ?_⟩
  · rw [hpartner]; nlinarith
  · rw [restrictedSum_mul_primes hp hq hne, hpartner]
    rw [hc1]
    ring

