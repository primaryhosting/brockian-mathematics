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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block above is repeated as a plain comment on the very first line of the
file; Lean requires `import` commands to precede any module docstring.)

## Contents

A *unitary divisor* of `n` is a divisor `d` with `gcd d (n / d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 n`.
Exactly five unitary perfect numbers are known
(`6`, `60`, `90`, `87360`, `146361946186458562560000`), and whether a sixth one
exists is an open problem; consequently the target statement here is a
*conditional reduction* rather than an unconditional existence proof.

We develop:

* `sigmaStar_mul_of_coprime`: `σ*` is multiplicative on coprime arguments;
* `sigmaStar_prime_pow`: `σ*(p ^ a) = p ^ a + 1`;
* verification that each of the five known numbers is unitary perfect;
* `not_isUnitaryPerfect_of_odd`: there is no odd unitary perfect number;
* `SixthUnitaryPerfectExists`: if some unitary perfect number exceeds the largest
  known one, then a unitary perfect number outside the known five exists.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem sigmaStar_fifth : sigmaStar 146361946186458562560000 = 292723892372917125120000 := by
  have h313 : sigmaStar 313 = 314 :=
    sigmaStar_step (p := 313) (a := 1) (m := 1) (by norm_num) one_ne_zero one_ne_zero
      (by norm_num) (by norm_num) sigmaStar_one (by norm_num)
  have h157 : sigmaStar 49141 = 49612 :=
    sigmaStar_step (p := 157) (a := 1) (m := 313) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h313 (by norm_num)
  have h109 : sigmaStar 5356369 = 5457320 :=
    sigmaStar_step (p := 109) (a := 1) (m := 49141) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h157 (by norm_num)
  have h79 : sigmaStar 423153151 = 436585600 :=
    sigmaStar_step (p := 79) (a := 1) (m := 5356369) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h109 (by norm_num)
  have h37 : sigmaStar 15656666587 = 16590252800 :=
    sigmaStar_step (p := 37) (a := 1) (m := 423153151) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h79 (by norm_num)
  have h19 : sigmaStar 297476665153 = 331805056000 :=
    sigmaStar_step (p := 19) (a := 1) (m := 15656666587) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h37 (by norm_num)
  have h13 : sigmaStar 3867196646989 = 4645270784000 :=
    sigmaStar_step (p := 13) (a := 1) (m := 297476665153) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h19 (by norm_num)
  have h11 : sigmaStar 42539163116879 = 55743249408000 :=
    sigmaStar_step (p := 11) (a := 1) (m := 3867196646989) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h13 (by norm_num)
  have h7 : sigmaStar 297774141818153 = 445945995264000 :=
    sigmaStar_step (p := 7) (a := 1) (m := 42539163116879) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h11 (by norm_num)
  have h5 : sigmaStar 186108838636345625 = 279162193035264000 :=
    sigmaStar_step (p := 5) (a := 4) (m := 297774141818153) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h7 (by norm_num)
  have h3 : sigmaStar 558326515909036875 = 1116648772141056000 :=
    sigmaStar_step (p := 3) (a := 1) (m := 186108838636345625) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) h5 (by norm_num)
  exact sigmaStar_step (p := 2) (a := 18) (m := 558326515909036875) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h3 (by norm_num)

