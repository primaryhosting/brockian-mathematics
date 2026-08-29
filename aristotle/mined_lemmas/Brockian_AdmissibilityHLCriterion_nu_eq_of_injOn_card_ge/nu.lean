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
  Target theorem `nu_eq_of_injOn_card_ge` for the corpus module
  `Brockian.AdmissibilityHLCriterion`.

  The corpus modules themselves are not part of this project, so the two corpus
  definitions the goal is phrased in terms of (`residueImage` and `nu`) are
  reproduced here verbatim, in their original namespace, purely so that the
  statement elaborates.  Nothing else from the corpus is restated or re-proved.
-/

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

def nu (p : ℕ) (H : Finset ℤ) : ℕ := (residueImage p H).card

/-- If the reduction map is injective on `S` and `S` has at least `p` elements, then
`S` meets every residue class mod `p`, i.e. `ν_p(S) = p`. -/
