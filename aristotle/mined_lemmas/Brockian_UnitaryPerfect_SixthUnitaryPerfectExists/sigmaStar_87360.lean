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

theorem sigmaStar_87360 : sigmaStar 87360 = 174720 := by
  have h13 : sigmaStar 13 = 14 :=
    sigmaStar_step (p := 13) (a := 1) (m := 1) (by norm_num) one_ne_zero one_ne_zero
      (by norm_num) (by norm_num) sigmaStar_one (by norm_num)
  have h91 : sigmaStar 91 = 112 :=
    sigmaStar_step (p := 7) (a := 1) (m := 13) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h13 (by norm_num)
  have h455 : sigmaStar 455 = 672 :=
    sigmaStar_step (p := 5) (a := 1) (m := 91) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h91 (by norm_num)
  have h1365 : sigmaStar 1365 = 2688 :=
    sigmaStar_step (p := 3) (a := 1) (m := 455) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h455 (by norm_num)
  exact sigmaStar_step (p := 2) (a := 6) (m := 1365) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h1365 (by norm_num)

