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

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

theorem not_admissible_of_eleven_dilated_residues :
    ¬ Admissible ({0, 12, 24, 36, 48, 60, 72, 84, 96, 108, 120} : Finset ℤ) := by
  intro h
  obtain ⟨r, hr⟩ := h 11 (by norm_num)
  exact hr (by revert r; decide)

end Brockian.AdmissibilityHLCriterion

