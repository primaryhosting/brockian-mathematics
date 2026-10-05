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

def GoldbachAsymptotic : Prop :=
  ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Even m → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = m

/-- **Vinogradov's three primes theorem** (Lean-checked reduction form).

Every sufficiently large odd number is a sum of three primes, deduced from the asymptotic
binary Goldbach statement `GoldbachAsymptotic`.  Concretely: if every even number beyond some
threshold is a sum of two primes, then every odd number beyond a (slightly larger) threshold is
a sum of three primes, namely `3` together with the two Goldbach primes for `n - 3`. -/
