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

theorem isKHyperperfect_six_threehundredone : IsKHyperperfect 6 301 := by
  refine ⟨by norm_num, ?_⟩
  simp only [restrictedSum, sigmaSum]
  decide

/-- Characterisation: for `n > 1`, `n` is hyperperfect exactly when the sum of its divisors
other than `1` and `n` is positive (i.e. `n` is composite) and divides `n - 1`. -/
