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
import Brockian.RieselCovering

/-!
# Riesel Problem — Mathlib interface

Companion to `Brockian.RieselCovering` (which is import-free): the same result phrased with
Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering

/-- `509203 * 2 ^ n - 1` is not prime for any `n ≥ 1`, stated with `Nat.Prime`. -/

def coveringDivisor (n : Nat) : Nat := coveringTable.getD (n % 24) 3

set_option maxRecDepth 10000 in
/-- The finite verification underlying the covering argument: for every residue `r < 24`
the tabulated divisor is a nontrivial divisor of `2 ^ 24 - 1 = 16777215` and of
`509203 * 2 ^ r - 1`. -/
