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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is **`k`-hyperperfect** if `n = 1 + k * (σ₁(n) - n - 1)`, i.e. `n` is one more than
`k` times the sum of the divisors of `n` other than `1` and `n`.  The defining equation is
stated in subtraction-free form: `n + k * (n + 1) = 1 + k * σ₁(n)`. -/
