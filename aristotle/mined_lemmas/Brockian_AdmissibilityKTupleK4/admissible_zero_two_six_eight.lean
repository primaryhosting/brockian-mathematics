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

namespace Brockian

/-- A `k`-tuple of integers `h : Fin k → ℤ` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the values
`h 0, …, h (k-1)` do not cover every residue class modulo `p`. -/

theorem admissible_zero_two_six_eight :
    Admissible ![(0 : ℤ), 2, 6, 8] := by
  rw [AdmissibilityKTupleK4]
  constructor
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩

#print axioms AdmissibilityKTupleK4
#print axioms admissible_zero_two_six_eight

end Brockian

