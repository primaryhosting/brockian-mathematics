/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- Fermat's Last Theorem for the exponent `n`, stated directly in terms of positive
integers: there are no positive naturals `x, y, z` with `x ^ n + y ^ n = z ^ n`. -/

theorem FLTFor_three : FLTFor 3 :=
  (FLTFor_iff_fermatLastTheoremFor 3).2 fermatLastTheoremThree

/-- Base case `n = 4` (Fermat): `x ^ 4 + y ^ 4 = z ^ 4` has no positive solutions. -/
