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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.HyperperfectNumbers

open scoped BigOperators

/-- `n` is `k`-hyperperfect if `n > 1` and `n = 1 + k * (σ(n) - n - 1)`, i.e. `n` is one plus
`k` times the sum of the divisors of `n` other than `1` and `n`. -/

lemma isHyperperfect_of_factorization {k d e : ℕ} (hk : 1 ≤ k) (hde : d * e = k ^ 2 + 1)
    (hp : Nat.Prime (k + d)) (hq : Nat.Prime (k + e)) :
    IsHyperperfect k ((k + d) * (k + e)) := by
  have hne : k + d ≠ k + e := by
    intro h
    have hd : d = e := by omega
    subst hd
    have h1 : k < d := by nlinarith
    have h2 : d ≤ k := by nlinarith
    omega
  rw [isHyperperfect_prime_mul_prime_iff hp hq hne]
  nlinarith [hde]

/-- The Brockian hypothesis: for every `k ≥ 1` the number `k ^ 2 + 1` admits a factorisation
`d * e` such that both `k + d` and `k + e` are prime. -/
