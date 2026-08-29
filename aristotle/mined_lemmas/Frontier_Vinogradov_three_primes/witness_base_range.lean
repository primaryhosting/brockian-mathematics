import Mathlib

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- `IsSumOfThreePrimes n` says that `n` is a sum of three (not necessarily distinct) primes. -/

lemma witness_base_range : ∀ k ∈ List.range 250, threePrimeWitness (2 * k + 9) = true := by
  decide

/-- Unconditional base case: every odd `n` with `9 ≤ n ≤ 507` is a sum of three primes.
(Verified by an explicit kernel computation.) -/
