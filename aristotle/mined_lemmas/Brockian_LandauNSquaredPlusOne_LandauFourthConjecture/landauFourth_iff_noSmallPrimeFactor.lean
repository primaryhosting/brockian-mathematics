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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace LandauNSquaredPlusOne

open Set

/-- The set of natural numbers `n` for which `n ^ 2 + 1` is prime. -/

theorem landauFourth_iff_noSmallPrimeFactor :
    LandauFourthStatement ↔ NoSmallPrimeFactorInfinitelyOften := by
  constructor
  · intro h N
    obtain ⟨n, hn, hnN⟩ := h.exists_gt (max N 1)
    have h1 : 1 ≤ n := le_trans (le_max_right N 1) hnN.le
    exact ⟨n, lt_of_le_of_lt (le_max_left N 1) hnN,
      no_small_prime_factor_of_prime h1 hn⟩
  · exact LandauFourthConjecture

end LandauNSquaredPlusOne
end Brockian

