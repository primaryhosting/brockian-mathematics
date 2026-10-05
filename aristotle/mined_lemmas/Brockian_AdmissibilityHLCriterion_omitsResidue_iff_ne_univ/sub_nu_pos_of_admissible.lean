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
  Brockian/AdmissibilityHLCriterion.lean — the Hardy–Littlewood admissibility criterion.

  This file reproduces the supplied corpus module (minus the two statements that depend on
  the companion modules `Brockian.AdmissibilityKTuple` and
  `Brockian.AdmissibilityCriterionScaffold`, which are not available in this project), and
  adds the requested new result `admissible_prod_sub_nu_pos`.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Brockian.AdmissibilityHLCriterion

/-- The residue classes mod `p` occupied by a finite integer tuple `H`. -/

theorem sub_nu_pos_of_admissible {S : Finset ℤ} (h : Admissible S) {p : ℕ}
    (hp : p.Prime) : 0 < p - nu p S :=
  Nat.sub_pos_of_lt ((admissible_iff_nu_lt S).mp h p hp)

