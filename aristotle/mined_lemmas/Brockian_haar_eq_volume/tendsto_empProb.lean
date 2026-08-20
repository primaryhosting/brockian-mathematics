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

theorem tendsto_empProb {alpha : ℝ} (hirr : Irrational alpha) :
    Tendsto (empProb alpha) atTop (𝓝 haarProb) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  set g : C(AddCircle (1:ℝ), ℂ) :=
    ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hg
  have hc := tendsto_avg_continuous hirr g
  have hint : (∫ x, g x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))
      = ((∫ x, f x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))) : ℝ) : ℂ) :=
    integral_complex_ofReal
  rw [hint] at hc
  have hreal : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (orbitPoint alpha n))
      atTop (𝓝 (∫ x, f x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))) := by
    refine tendsto_ofReal_iff.mp ?_
    convert hc using 2 with N
    simp only [hg, ContinuousMap.coe_mk]
    push_cast
    ring
  refine (hreal.comp (tendsto_add_atTop_nat 1)).congr (fun k => ?_)
  simp only [Function.comp_apply]
  rw [show ((empProb alpha k : ProbabilityMeasure (AddCircle (1:ℝ))) :
      Measure (AddCircle (1:ℝ))) = empMeasure alpha (k+1) from rfl, integral_empMeasure]
  simp [smul_eq_mul]

/-! ### Arcs -/

/-- Two reals define the same point of `ℝ / ℤ` exactly when they differ by an integer. -/
