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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the divisors of `n` other than `n` itself). -/

lemma sum_divisors_eq (n : ℕ) : ∑ d ∈ n.divisors, d = properDivisorSum n + n :=
  Nat.sum_divisors_eq_sum_properDivisors_add_self

/-- Abstract form of the Thabit ibn Qurra rule: if `p + 1 = 3·2ⁿ`, `q + 1 = 6·2ⁿ`,
`r + 1 = 18·2ⁿ·2ⁿ` with `p, q, r` prime and `n ≥ 1`, then `2ⁿ⁺¹·p·q` and `2ⁿ⁺¹·r`
form an amicable pair. -/
