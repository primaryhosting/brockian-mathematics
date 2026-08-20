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
# Equidistribution of irrational rotations, and the density of configuration counts

This file proves Weyl's equidistribution theorem for the sequence `n ↦ {n α}` (`α` irrational)
and deduces the unconditional statement `configCount_density_of_BV`: the density of the set of
`n < N` with `{n α} ∈ [a, b)` tends to `b - a`.

The indicator of an interval is the basic example of a function of bounded variation, and the
"BV reduction" is implemented here through the portmanteau theorem: the empirical measures of
the orbit converge weakly to Haar measure (proved via the Fourier/Weyl criterion), hence the
measures of any arc whose boundary is Haar-null converge.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter MeasureTheory Set Topology AddCircle
open scoped BigOperators ENNReal NNReal

/-- The point `n • α` of the circle `ℝ / ℤ`. -/

theorem configCount_density_of_BV {alpha a b : ℝ} (hirr : Irrational alpha)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  have hfront : ((haarProb : ProbabilityMeasure (AddCircle (1:ℝ))) : Measure (AddCircle (1:ℝ)))
      (frontier (arc a b)) = 0 := haar_frontier_arc a b
  have hw := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (tendsto_empProb hirr) hfront
  rw [show ((haarProb : ProbabilityMeasure (AddCircle (1:ℝ))) : Measure (AddCircle (1:ℝ)))
      = haarAddCircle from rfl, haar_arc ha hab hb] at hw
  have hw2 := (ENNReal.tendsto_toReal (by simp)).comp hw
  rw [ENNReal.toReal_ofReal (by linarith)] at hw2
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine hw2.congr (fun k => ?_)
  simp only [Function.comp_apply]
  rw [show ((empProb alpha k : ProbabilityMeasure (AddCircle (1:ℝ))) :
      Measure (AddCircle (1:ℝ))) = empMeasure alpha (k+1) from rfl, empMeasure_arc ha hb]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    div_eq_inv_mul]

end EquidistributionBVReduction
end Brockian

