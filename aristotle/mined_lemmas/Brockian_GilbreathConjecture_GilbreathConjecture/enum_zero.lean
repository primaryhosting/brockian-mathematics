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

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/

theorem enum_zero {p : Nat → Nat} (hp : IsPrimeEnumeration p) : p 0 = 2 := by
  obtain ⟨n, hn⟩ := hp.2.2 2 (by decide)
  have h1 : p 0 ≤ p n := enum_le hp (Nat.zero_le n)
  have h2 : 2 ≤ p 0 := (hp.1 0).1
  omega

/-- One step along the enumeration: if `p k = q`, `r` is the next prime after `q`
(no prime lies strictly between), then `p (k + 1) = r`. -/
