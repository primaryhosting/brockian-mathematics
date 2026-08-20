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

theorem tendsto_avg_continuous {alpha : ℝ} (hirr : Irrational alpha) (f : C(AddCircle (1:ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (orbitPoint alpha n))
      atTop (𝓝 (∫ x, f x ∂haarAddCircle)) := by
  have hdense : f ∈ closure ((Submodule.span ℂ (Set.range (@fourier 1))) :
      Set C(AddCircle (1:ℝ), ℂ)) := by
    have h := span_fourier_closure_eq_top (T := (1:ℝ))
    have h' : ((Submodule.span ℂ (Set.range (@fourier 1))).topologicalClosure :
        Set C(AddCircle (1:ℝ), ℂ)) = (⊤ : Submodule ℂ C(AddCircle (1:ℝ), ℂ)) := by rw [h]
    rw [Submodule.topologicalClosure_coe] at h'
    rw [h']
    trivial
  refine tendsto_of_approx (u := orbitAvg alpha f) ?_
  intro ε hε
  rw [Metric.mem_closure_iff] at hdense
  obtain ⟨g, hg, hfg⟩ := hdense ε hε
  refine ⟨orbitAvg alpha g, ∫ x, g x ∂haarAddCircle,
    tendsto_orbitAvg_of_mem_span hirr g hg, fun n => ?_, ?_⟩
  · exact le_trans (orbitAvg_dist alpha f g n) (by rw [← dist_eq_norm]; exact hfg.le)
  · exact le_trans (integral_dist g f) (by rw [← dist_eq_norm, dist_comm]; exact hfg.le)

/-! ### Empirical measures -/

instance empMeasure_isProbabilityMeasure (alpha : ℝ) (k : ℕ) :
    IsProbabilityMeasure (empMeasure alpha (k+1)) := by
  constructor
  rw [empMeasure, Measure.smul_apply, Measure.finset_sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  rw [ENNReal.inv_mul_cancel] <;> simp

