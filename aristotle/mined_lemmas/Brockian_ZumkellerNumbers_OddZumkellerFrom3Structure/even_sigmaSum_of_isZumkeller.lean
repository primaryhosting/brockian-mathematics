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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- The sum-of-divisors function `σ₁`, written directly as a sum over `Nat.divisors`. -/

theorem even_sigmaSum_of_isZumkeller {n : ℕ} (hz : IsZumkeller n) : Even (sigmaSum n) := by
  obtain ⟨-, S, hS, hsum⟩ := hz
  have h := Finset.sum_sdiff (f := fun d : ℕ => d) hS
  refine ⟨∑ d ∈ S, d, ?_⟩
  rw [sigmaSum, ← h, ← hsum]

/-- A Zumkeller number is perfect or abundant: `2n ≤ σ(n)`. -/
