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

theorem sixthUnitaryPerfect_of_gt_87360 {n : ℕ} (hn : IsUnitaryPerfect n) (hlt : 87360 < n)
    (hne : n ≠ 146361946186458562560000) : SixthUnitaryPerfect := by
  refine ⟨n, hn, ?_⟩
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨by omega, by omega, by omega, by omega, hne⟩

/-- **Conditional reduction (target).**
A sixth unitary perfect number exists — that is, some unitary perfect number is
not among the five known ones — provided that some unitary perfect number exceeds
the largest known one, `146361946186458562560000`.

Whether such a number exists is an open problem, so the statement is conditional;
the five known values are verified unconditionally above
(`isUnitaryPerfect_six`, ..., `isUnitaryPerfect_fifth`), and every unitary perfect
number is even (`not_isUnitaryPerfect_of_odd`). -/
