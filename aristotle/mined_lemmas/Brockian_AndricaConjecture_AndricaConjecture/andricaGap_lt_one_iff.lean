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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.AndricaConjecture

open Real

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`). -/

lemma andricaGap_lt_one_iff (n : ℕ) :
    andricaGap n < 1 ↔
      (nthPrime (n + 1) : ℝ) < (nthPrime n : ℝ) + 2 * Real.sqrt (nthPrime n) + 1 := by
  simpa [andricaGap] using
    sqrt_sub_sqrt_lt_one_iff (a := (nthPrime n : ℝ)) (b := (nthPrime (n + 1) : ℝ))
      (by positivity)

/-- **Reduction of the Andrica conjecture to a prime-gap bound.** The Andrica conjecture
`√p_{n+1} - √p_n < 1` for all `n` is *equivalent* to the bound
`p_{n+1} < p_n + 2√p_n + 1` for all `n`. -/
