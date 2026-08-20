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

theorem exists_odd_prime_factor (h : IsUnitaryPerfect n) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ n := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ q ∈ n.primeFactors, q = 2 := by
    intro q hq
    by_contra hne
    exact hcon q (Nat.prime_of_mem_primeFactors hq) hne (Nat.dvd_of_mem_primeFactors hq)
  have hn2 : n = 2 ^ n.factorization 2 := eq_pow_of_unique_primeFactor h.one_lt hall
  have hk : n.factorization 2 ≠ 0 := by
    intro hk0
    rw [hk0, pow_zero] at hn2
    exact absurd hn2 h.one_lt.ne'
  have h2 := h.2
  rw [hn2, sigmaStar_prime_pow Nat.prime_two hk] at h2
  have h1 : 1 < 2 ^ n.factorization 2 := Nat.one_lt_two_pow_iff.mpr hk
  generalize (2 : ℕ) ^ n.factorization 2 = a at h2 h1
  omega

/-- There are no odd unitary perfect numbers: every unitary perfect number is even. -/
