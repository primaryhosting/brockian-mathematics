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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Brockian
namespace GilbreathConjecture

/-! ## The Gilbreath triangle and the statement of the conjecture -/

/-- `gilbreathRow n k` is the `k`-th entry (0-indexed) of the `n`-th row of the
Gilbreath triangle: row `0` is the sequence of primes `2, 3, 5, 7, 11, ...` and each
subsequent row is obtained by taking absolute values of consecutive differences. -/

theorem gilbreath_of_le_108 (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 108) : gilbreathRow n 0 = 1 := by
  by_cases h : n ≤ 3
  · exact head_eq_one_of_goodRow goodRow_one h1 (by omega)
  by_cases ha : n ≤ 16
  · exact head_eq_one_of_goodRow goodRow_three (by omega) (by omega)
  by_cases hb : n ≤ 29
  · exact head_eq_one_of_goodRow goodRow_five (by omega) (by omega)
  by_cases hc : n ≤ 68
  · exact head_eq_one_of_goodRow goodRow_ten (by omega) (by omega)
  · exact head_eq_one_of_goodRow goodRow_eleven (by omega) (by omega)

end GilbreathConjecture
end Brockian

