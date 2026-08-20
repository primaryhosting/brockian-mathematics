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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
## Practical numbers and practical twins

A positive integer `n` is *practical* if every `m ≤ σ(n)` is a sum of distinct divisors of `n`.
The *practical twin* problem asks whether there are infinitely many `n` such that both `n` and
`n + 2` are practical (this is a known but genuinely deep statement, proved by sieve methods;
no unconditional proof is formalised here).

This file develops:

* `IsPractical`, `DivisorComplete` and the equivalence `isPractical_iff_divisorComplete`
  between practicality and the elementary divisor-chain criterion "every divisor is at most one
  more than the sum of the smaller divisors";
* decidability of the criterion, and explicit practical twin pairs up to `(8190, 8192)`;
* `isPractical_two_pow`, `infinite_practical`: powers of two are practical, so there are
  infinitely many practical numbers;
* `isPractical_mul_prime`: the coprime case of Stewart's multiplication theorem, and the family
  `isPractical_prime_mul_two_pow`;
* `practicalTwinConjecture_iff` and `PracticalTwinInfinitude`: a Lean-checked reduction of the
  practical twin conjecture to the elementary criterion.
-/

set_option maxRecDepth 10000

open Finset

namespace Brockian.PracticalNumbers

/-- A positive integer `n` is *practical* if every `m ≤ σ(n)` is the sum of a set of
pairwise distinct divisors of `n`. -/

theorem isPractical_prime_mul_two_pow {p a : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hle : p ≤ 2 ^ (a + 1)) : IsPractical (p * 2 ^ a) := by
  refine isPractical_mul_prime (isPractical_two_pow a) hp ?_ ?_
  · intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
    exact hodd this
  · rw [sum_divisors_two_pow]
    have : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    omega

/-- Explicit practical twin pairs: `(2,4)`, `(4,6)`, `(6,8)`, `(16,18)`, `(30,32)`,
`(126,128)`, `(2046,2048)` and `(8190,8192)`. -/
