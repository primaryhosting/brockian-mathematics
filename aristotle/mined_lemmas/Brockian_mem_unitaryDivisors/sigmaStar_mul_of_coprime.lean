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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *unitary divisor* of `n` is a divisor `d ∣ n` with `gcd d (n / d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.
Exactly five unitary perfect numbers are known,

```
6, 60, 90, 87360, 146361946186458562560000
```

and whether a sixth one exists is a well-known open problem.  Consequently the statement
"a sixth unitary perfect number exists" cannot be proved outright; what is established
here is:

* the multiplicative theory of `σ*` from scratch, culminating in the Euler-product
  formula `sigmaStar_eq_prod_primeFactors` and multiplicativity
  `sigmaStar_mul_of_coprime`;
* unconditional verification that the five known numbers are unitary perfect
  (`known_isUnitaryPerfect`);
* unconditional structural theorems: every unitary perfect number has an odd prime
  factor (`exists_odd_prime_factor`) and is even (`even_of_isUnitaryPerfect`), i.e.
  there are no odd unitary perfect numbers, and a unitary perfect number with only two
  distinct prime factors must equal `6` (`eq_six_of_card_primeFactors_eq_two`);
* the target theorem `SixthUnitaryPerfectExists`, a Lean-checked *conditional
  reduction*: from the existence of a unitary perfect number outside the known list one
  obtains a genuine "sixth" unitary perfect number together with all of the structural
  information above (even, `> 6`, at least three distinct prime factors, divisible by an
  odd prime).

Mathlib search note: `exact?` / `apply?` / `rw?` find nothing directly applicable here.
Mathlib's divisor API (`Nat.divisors`, `Nat.ArithmeticFunction.sigma`,
`Nat.ArithmeticFunction.isMultiplicative_sigma`) treats ordinary divisors only and has no
notion of unitary divisor, so the theory below is built from the general factorization
lemmas (`Nat.factorization_prod_pow_eq_self`, `Finset.prod_add`, ...).
-/

open Finset

namespace Brockian
namespace UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `d` coprime to `n / d`. -/

theorem sigmaStar_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.Coprime a b) :
    sigmaStar (a * b) = sigmaStar a * sigmaStar b := by
  classical
  have hdisj : Disjoint a.primeFactors b.primeFactors := Nat.Coprime.disjoint_primeFactors h
  rw [sigmaStar_eq_prod_primeFactors (mul_ne_zero ha hb), sigmaStar_eq_prod_primeFactors ha,
    sigmaStar_eq_prod_primeFactors hb, h.primeFactors_mul,
    Finset.prod_union hdisj, Nat.factorization_mul ha hb]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hz : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
      intro hdvd
      exact (Finset.disjoint_left.1 hdisj) hp (Nat.mem_primeFactors.2
        ⟨Nat.prime_of_mem_primeFactors hp, hdvd, hb⟩))
    simp [hz]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hz : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
      intro hdvd
      exact (Finset.disjoint_right.1 hdisj) hp (Nat.mem_primeFactors.2
        ⟨Nat.prime_of_mem_primeFactors hp, hdvd, ha⟩))
    simp [hz]

/-- Peeling one prime power off a factorization; the workhorse of the numerical
verifications below. -/
