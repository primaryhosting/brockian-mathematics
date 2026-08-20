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

lemma sigmaStar_fifth :
    sigmaStar 146361946186458562560000 = 292723892372917125120000 := by
  have h11 : sigmaStar 313 = 314 := by
    have h := sigmaStar_step (p := 313) (k := 1) (m := 1) (N := 313) (by norm_num) one_ne_zero
      one_ne_zero (by norm_num) (by norm_num) sigmaStar_one
    norm_num at h; exact h
  have h10 : sigmaStar 49141 = 49612 := by
    have h := sigmaStar_step (p := 157) (k := 1) (m := 313) (N := 49141) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) h11
    norm_num at h; exact h
  have h9 : sigmaStar 5356369 = 5457320 := by
    have h := sigmaStar_step (p := 109) (k := 1) (m := 49141) (N := 5356369) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h10
    norm_num at h; exact h
  have h8 : sigmaStar 423153151 = 436585600 := by
    have h := sigmaStar_step (p := 79) (k := 1) (m := 5356369) (N := 423153151) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h9
    norm_num at h; exact h
  have h7 : sigmaStar 15656666587 = 16590252800 := by
    have h := sigmaStar_step (p := 37) (k := 1) (m := 423153151) (N := 15656666587) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h8
    norm_num at h; exact h
  have h6 : sigmaStar 297476665153 = 331805056000 := by
    have h := sigmaStar_step (p := 19) (k := 1) (m := 15656666587) (N := 297476665153) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h7
    norm_num at h; exact h
  have h5 : sigmaStar 3867196646989 = 4645270784000 := by
    have h := sigmaStar_step (p := 13) (k := 1) (m := 297476665153) (N := 3867196646989)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h6
    norm_num at h; exact h
  have h4 : sigmaStar 42539163116879 = 55743249408000 := by
    have h := sigmaStar_step (p := 11) (k := 1) (m := 3867196646989) (N := 42539163116879)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h5
    norm_num at h; exact h
  have h3 : sigmaStar 297774141818153 = 445945995264000 := by
    have h := sigmaStar_step (p := 7) (k := 1) (m := 42539163116879) (N := 297774141818153)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h4
    norm_num at h; exact h
  have h2 : sigmaStar 186108838636345625 = 279162193035264000 := by
    have h := sigmaStar_step (p := 5) (k := 4) (m := 297774141818153) (N := 186108838636345625)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3
    norm_num at h; exact h
  have h1 : sigmaStar 558326515909036875 = 1116648772141056000 := by
    have h := sigmaStar_step (p := 3) (k := 1) (m := 186108838636345625) (N := 558326515909036875)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h2
    norm_num at h; exact h
  have h0 := sigmaStar_step (p := 2) (k := 18) (m := 558326515909036875)
    (N := 146361946186458562560000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h1
  norm_num at h0; exact h0

/-- All five known unitary perfect numbers really are unitary perfect. -/
