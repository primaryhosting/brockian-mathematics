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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

(The requested header appears at the very top of this file as a plain block comment rather than
as a module docstring, because Lean requires every `import` to precede any module docstring.)

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` with the same sum of prime
factors counted with multiplicity (`sopfr`), e.g. `(714, 715)`: `714 = 2·3·7·17` and
`715 = 5·11·13`, both with factor sum `29`.

Whether there are infinitely many Ruth–Aaron pairs is an open problem (Erdős conjectured that
there are).  This file contains:

* the basic theory of `sopfr` (additivity, `sopfr n ≤ n`, value at primes);
* verification of the first Ruth–Aaron pairs `5, 8, 15, 77, 125, 714`;
* two *unconditional* partial results: `sopfr n - sopfr (n+1)` is positive infinitely often and
  negative infinitely often, i.e. the difference changes sign infinitely often (a Ruth–Aaron pair
  is exactly a place where the difference vanishes);
* an *unconditional* structural obstruction, `no_prime_semiprime_pair` /
  `not_isRuthAaronPair_of_semiprimes`: no Ruth–Aaron pair consists of two semiprimes, i.e.
  `p * q + 1 = r * s` together with `p + q = r + s` is impossible for primes `p, q, r, s`
  (this rules out the simplest conceivable parametric families);
* a *conditional reduction*: `RuthAaronInfinitude` derives the infinitude of Ruth–Aaron pairs
  from `PrimeFactorizationHypothesis`, a statement phrased purely in terms of lists of primes
  (arbitrarily large products of primes `L` whose product is one less than the product of a list
  `M` of primes with the same sum), with no reference to the factorization function.
  `ruthAaron_infinite_iff` shows that the reduction loses nothing: the hypothesis is in fact
  equivalent to the infinitude statement.
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity.
By convention `sopfr 0 = sopfr 1 = 0`. -/

lemma sopfr_two_mul_lt {m : ℕ} (hm : 2 ≤ m) : sopfr (2 * m) < 2 * m + 1 := by
  have h : sopfr (2 * m) = 2 + sopfr m := by
    rw [sopfr_mul (by norm_num) (by omega)]
    simp [sopfr_prime Nat.prime_two]
  have := sopfr_le_self m
  omega

/-- Every prime `p ≥ 7` is of the form `2 * m + 1` with `3 ≤ m`. -/
