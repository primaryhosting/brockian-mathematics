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

/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *`k`-hyperperfect* when `n = 1 + k * (σ n - n - 1)`, where `σ` is the
sum-of-divisors function.  For `k = 1` these are exactly the perfect numbers.  The conjecture
addressed here states that **for every `k ≥ 1` there exists a `k`-hyperperfect number**; this is
an open problem (no `5`-hyperperfect number is known, for instance).

This file contains:

* the basic theory (`sigma`, `IsHyperperfect`, and the usual integer form of the equation);
* an exact characterisation of the hyperperfect numbers of the shape `m * q` with `q` a prime not
  dividing `m` (`isHyperperfect_mul_prime_iff`), and the resulting construction
  (`isHyperperfect_of_seed`);
* the classical semiprime family: if `k + 1` and `k ^ 2 + k + 1` are prime then
  `(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect (`isHyperperfect_classical`), together with the
  full semiprime characterisation `(p - k) * (q - k) = k ^ 2 + 1`;
* unconditional witnesses for a number of small `k` (`exists_hyperperfect_of_small`);
* the main target `HyperperfectAllK`: a Lean-checked reduction of the conjecture to the
  arithmetic hypothesis `SeedHypothesis`.
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigma n` is the sum of the (positive) divisors of `n`, usually written `σ(n)`. -/

theorem isHyperperfect_prime_mul_prime_iff {k a b : ℕ} (ha : (k + a).Prime) (hb : (k + b).Prime)
    (hab : k + a ≠ k + b) :
    IsHyperperfect k ((k + a) * (k + b)) ↔ a * b = k ^ 2 + 1 := by
  have hs : sigma ((k + a) * (k + b)) = (k + a + 1) * (k + b + 1) :=
    sigma_prime_mul_prime ha hb hab
  have hn : 1 < (k + a) * (k + b) := by
    have h2a := ha.two_le
    have h2b := hb.two_le
    nlinarith
  unfold IsHyperperfect
  rw [hs]
  constructor
  · rintro ⟨-, h⟩
    zify at h ⊢
    linarith [h]
  · intro h
    refine ⟨hn, ?_⟩
    zify at h ⊢
    linear_combination -h

/-- A number of the shape `k ^ 2 + 1` is never a perfect square when `k ≥ 1`; hence in a
factorisation `a * b = k ^ 2 + 1` the two factors differ. -/
