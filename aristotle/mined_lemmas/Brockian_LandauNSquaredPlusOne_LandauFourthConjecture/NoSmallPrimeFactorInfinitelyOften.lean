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

def NoSmallPrimeFactorInfinitelyOften : Prop :=
  ∀ N : ℕ, ∃ n > N, ∀ p : ℕ, p.Prime → p ∣ n ^ 2 + 1 → n < p

/-! ### Elementary facts about `n ^ 2 + 1` -/

/-- If every prime factor of `n ^ 2 + 1` exceeds `n` (and `n ≥ 1`), then `n ^ 2 + 1` is prime. -/
