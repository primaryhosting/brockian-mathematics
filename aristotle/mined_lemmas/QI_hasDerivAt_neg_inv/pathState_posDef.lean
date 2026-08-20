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

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem pathState_posDef (hρ : ρ.PosDef) (hσ : σ.PosDef) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (pathState ρ σ s).PosDef := by
  rw [pathState_eq]
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    simpa using hρ
  · refine Matrix.PosDef.add_posSemidef (hσ.smul ?_) (hρ.posSemidef.smul ?_)
    · have : (0:ℝ) < 1 - s := by linarith
      exact_mod_cast this
    · exact_mod_cast h0

