import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
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

open Filter MeasureTheory Metric

/-! ## Auxiliary lemmas -/

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/

theorem liminf_add_le_liminf_add_nat (u v : ℕ → ENNReal) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  simp only [Filter.liminf_eq_iSup_iInf_of_nat]
  refine ENNReal.iSup_add_iSup_le ?_
  intro i j
  refine le_trans ?_ (le_iSup _ (max i j))
  refine le_iInf₂ (fun m hm => add_le_add ?_ ?_)
  · exact iInf₂_le m (le_trans (le_max_left i j) hm)
  · exact iInf₂_le m (le_trans (le_max_right i j) hm)

/-- Superadditivity of `liminf` for a finite sum of `ℝ≥0∞`-valued sequences. -/
