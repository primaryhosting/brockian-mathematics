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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

theorem isHyperperfect_of_primes {k : ℕ} (hk : 0 < k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k ^ 2 + k + 1)) :
    IsHyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have e : k ^ 2 + k + 1 = k + (k ^ 2 + 1) := by ring
  have hne : k + 1 ≠ k + (k ^ 2 + 1) := by
    have : 0 < k ^ 2 := by positivity
    omega
  have h := isHyperperfect_of_factorization (k := k) (a := 1) (b := k ^ 2 + 1)
    (by ring) (by simpa using hp) (by rw [← e]; exact hq) hne
  simpa [← e] using h

/-! ## Main statement -/

/-- **Main theorem (partial and conditional forms of "hyperperfect numbers exist for all `k`").**

The Brockian conjecture `HyperperfectAllKConjecture` asserts that a `k`-hyperperfect number exists
for every `k ≥ 1`; it is open.  This theorem records what can be proved unconditionally:

* for every `k ≥ 1` for which `k + 1` and `k ^ 2 + k + 1` are both prime, the number
  `(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect (so such `k` are settled);
* conversely, the whole conjecture follows from the purely prime-theoretic statement that for
  every `k ≥ 1` the number `k ^ 2 + 1` admits a factorization `a * b` with `k + a` and `k + b`
  distinct primes;
* and this prime-theoretic statement is not merely sufficient but *necessary* for the
  two-prime (semiprime) witnesses: a product of two distinct primes `p * q` is `k`-hyperperfect
  if and only if `k < p`, `k < q` and `(p - k) * (q - k) = k ^ 2 + 1`. -/
