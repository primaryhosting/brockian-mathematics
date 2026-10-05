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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

theorem thabit_pair_zero :
    IsAmicablePair (2 ^ (0 + 2) * (3 * 2 ^ (0 + 1) - 1) * (3 * 2 ^ (0 + 2) - 1))
      (2 ^ (0 + 2) * (9 * 2 ^ (2 * 0 + 3) - 1)) ∧
    2 ^ (0 + 2) * (3 * 2 ^ (0 + 1) - 1) * (3 * 2 ^ (0 + 2) - 1) = 220 ∧
    2 ^ (0 + 2) * (9 * 2 ^ (2 * 0 + 3) - 1) = 284 :=
  ⟨isAmicablePair_of_thabitIndex thabitIndex_zero, by norm_num, by norm_num⟩

/-- The Thâbit pair for `k = 2` is `(17296, 18416)`; in particular these are amicable. -/
