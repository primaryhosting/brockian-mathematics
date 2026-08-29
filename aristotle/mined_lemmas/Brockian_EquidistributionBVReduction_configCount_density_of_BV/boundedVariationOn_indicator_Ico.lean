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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ENNReal
open Set Filter MeasureTheory

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Variation of a difference -/

/-- The variation of a difference of two real-valued functions is at most the sum of the
variations. -/

theorem boundedVariationOn_indicator_Ico {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) := by
  have heq : eVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1)
      = eVariationOn (fun t => Set.indicator (Set.Ici a) (fun _ => (1 : ℝ)) t
          - Set.indicator (Set.Ici b) (fun _ => (1 : ℝ)) t) (Set.Icc (0 : ℝ) 1) :=
    eVariationOn.eq_of_eqOn fun t _ => indicator_Ico_eq_sub hab t
  show eVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) ≠ ⊤
  rw [heq]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
    ⟨boundedVariationOn_indicator_Ici a, boundedVariationOn_indicator_Ici b⟩)
    (eVariationOn_sub_le _ _ _)

/-- The integral of the indicator of `[a, b) ⊆ [0, 1]` over `[0, 1]` is `b - a`. -/
