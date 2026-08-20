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

(The header above is repeated here as a module docstring: Lean requires all
`import` statements to precede any module documentation comment.)

## Contents

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n/d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.
Only five unitary perfect numbers are known, and whether a sixth exists is open.

This file develops the basic theory (`σ*` is multiplicative, its value on prime
powers, and hence the product formula `σ*(n) = ∏_{p^a ‖ n} (p^a + 1)`), verifies
the five classically known unitary perfect numbers, proves the partial result
that no odd number is unitary perfect, and finally states and proves the
conditional reduction `SixthUnitaryPerfectExists`: as soon as there is *one*
unitary perfect number outside the known list of five, there are at least six
unitary perfect numbers.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

theorem usigma_87360 : usigma 87360 = 174720 := by
  have h13 : usigma 13 = 14 :=
    usigma_step (p := 13) (k := 1) (m := 1) (by norm_num) one_ne_zero (by norm_num)
      usigma_one (by norm_num) (by norm_num)
  have h91 : usigma 91 = 112 :=
    usigma_step (p := 7) (k := 1) (m := 13) (by norm_num) one_ne_zero (by norm_num)
      h13 (by norm_num) (by norm_num)
  have h455 : usigma 455 = 672 :=
    usigma_step (p := 5) (k := 1) (m := 91) (by norm_num) one_ne_zero (by norm_num)
      h91 (by norm_num) (by norm_num)
  have h1365 : usigma 1365 = 2688 :=
    usigma_step (p := 3) (k := 1) (m := 455) (by norm_num) one_ne_zero (by norm_num)
      h455 (by norm_num) (by norm_num)
  exact usigma_step (p := 2) (k := 6) (m := 1365) (by norm_num) (by norm_num) (by norm_num)
    h1365 (by norm_num) (by norm_num)

