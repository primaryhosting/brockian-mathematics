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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

set_option autoImplicit false

namespace Brockian.QuasiperfectNumbers

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of its divisors
equals `2 * n + 1` (equivalently, the sum of its proper divisors is `n + 1`).
No quasiperfect number is known, and their existence is an open problem. -/

theorem quasiperfect_iff_sum_divisors {n : ℕ} :
    Quasiperfect n ↔ 0 < n ∧ ∑ d ∈ n.divisors, d = 2 * n + 1 := by
  simp [Quasiperfect, sigma_one_apply]

/-! ### Auxiliary arithmetic lemmas -/

/-- If `D ≡ 3 [MOD 4]` then `D` divides no number of the form `m ^ 2 + 1`;
i.e. `-1` is not a square modulo such a `D`. -/
