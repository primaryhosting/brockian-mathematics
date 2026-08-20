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

namespace Frontier

open MeasureTheory intervalIntegral

/-- The Berry curvature `F₁₂ = ∂₁A₂ - ∂₂A₁` of a Berry connection `A = (A₁, A₂)` on the
Brillouin zone, given the two partial derivatives `d1A2 = ∂₁A₂` and `d2A1 = ∂₂A₁`. -/

lemma integrable_uncurry_of_continuous {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
    Integrable (Function.uncurry g)
      (((volume.restrict (Set.Ioc (0:ℝ) 1))).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
  rw [Measure.prod_restrict]
  have hcpt : IsCompact ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) :=
    (isCompact_Icc).prod isCompact_Icc
  have h1 : IntegrableOn (Function.uncurry g) ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) volume := by
    exact (hg.continuousOn).integrableOn_compact hcpt
  exact h1.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- Fubini on the unit square for continuous integrands. -/
