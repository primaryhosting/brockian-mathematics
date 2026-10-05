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

theorem andrica_iff_gap_bound :
    (∀ n : ℕ, andricaGap n < 1) ↔
      (∀ n : ℕ, (nthPrime (n + 1) : ℝ) < (nthPrime n : ℝ) + 2 * Real.sqrt (nthPrime n) + 1) :=
  forall_congr' fun n => andricaGap_lt_one_iff n

/-- **Andrica conjecture, conditional form.** Assuming the prime-gap bound
`p_{n+1} < p_n + 2√p_n + 1` (which is equivalent to it, see `andrica_iff_gap_bound`),
we have `√p_{n+1} - √p_n < 1` for every `n`.

The Andrica conjecture is an open problem, so the result is stated here in this
conditional (reduced) form. -/
