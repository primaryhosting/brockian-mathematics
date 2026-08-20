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
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The statement of Fermat's Last Theorem in explicit positive-integer form:
`x ^ n + y ^ n = z ^ n` has no solution in positive integers when `n > 2`. -/

theorem FLT_three : FermatLastTheoremFor 3 := fermatLastTheoremThree

/-- **Fermat's Last Theorem, reduced to odd prime exponents.**

`x ^ n + y ^ n = z ^ n` has no solution in positive integers for `n > 2` if and only if it has
no such solution for every odd prime exponent `p`.

The nontrivial direction uses the classical reduction: every `n ≥ 3` is divisible by `4` or by
an odd prime, the case of exponent `4` being Fermat's own descent argument, available in Mathlib
as `fermatLastTheoremFour`; divisibility of exponents transfers the statement via
`FermatLastTheoremFor.mono`. -/
