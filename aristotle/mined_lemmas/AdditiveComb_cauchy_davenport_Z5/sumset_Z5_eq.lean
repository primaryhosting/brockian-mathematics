/-
# Cauchy Davenport Z 5
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.cauchy_davenport_Z5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cauchy Davenport Z 5
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.cauchy_davenport_Z5
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

set_option grind.warning false

namespace AdditiveComb

/-- The sumset `{0,1} + {0,2}` in `ZMod 5` is `{0,1,2,3}`. -/

theorem sumset_Z5_eq :
    (({0, 1} : Finset (ZMod 5)) + ({0, 2} : Finset (ZMod 5)))
      = ({0, 1, 2, 3} : Finset (ZMod 5)) := by
  decide

/-- Cauchy–Davenport, concrete instance: in `ZMod 5`, for `A = {0,1}` and `B = {0,2}`,
the sumset `A + B = {0,1,2,3}` has cardinality `4`. -/
