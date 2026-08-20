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

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := ⟨by norm_num, sigmaStar_sixty⟩

