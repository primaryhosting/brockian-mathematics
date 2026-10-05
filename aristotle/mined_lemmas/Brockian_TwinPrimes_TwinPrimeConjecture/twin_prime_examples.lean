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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The twin prime conjecture itself is open, so what is proved here is a
*Lean-checked reduction*: the twin prime conjecture is shown to be equivalent to
an explicit elementary congruence condition (Clement's criterion), together with
some unconditional partial results.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `n` is the smaller member of a twin prime pair. -/

theorem twin_prime_examples :
    IsTwinPrime 3 ∧ IsTwinPrime 5 ∧ IsTwinPrime 11 ∧ IsTwinPrime 17 ∧ IsTwinPrime 29 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- Clement's criterion, checked on a small example: `3` and `5` are twin primes. -/
example : ClementCongruence 3 := (clement_criterion (by norm_num)).mp twin_prime_examples.1

/-- Every twin prime pair other than `(3,5)` has the form `(6k - 1, 6k + 1)`:
if `n` and `n+2` are prime and `n ≥ 5`, then `n % 6 = 5`. -/
