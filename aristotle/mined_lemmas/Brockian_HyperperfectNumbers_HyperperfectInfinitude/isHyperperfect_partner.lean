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

theorem isHyperperfect_partner {p : ℕ} (hp : p.Prime) (hq : (partner p).Prime) :
    IsHyperperfect (p * partner p) := by
  refine ⟨p - 1, ?_, isKHyperperfect_partner hp hq⟩
  have := hp.two_le
  omega

/-- **Hyperperfect Infinitude (conditional).** If there are infinitely many primes `p` for which
`p² - p + 1` is also prime (a Bunyakovsky/Schinzel-type hypothesis for the polynomial
`x² - x + 1`, beyond current unconditional methods), then there are infinitely many
hyperperfect numbers.

Each such `p` yields the hyperperfect number `p * (p² - p + 1)`, which is
`(p - 1)`-hyperperfect. -/
