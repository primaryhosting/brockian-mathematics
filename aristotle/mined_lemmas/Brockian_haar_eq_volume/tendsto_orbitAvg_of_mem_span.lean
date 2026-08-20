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

lemma tendsto_orbitAvg_of_mem_span {alpha : ℝ} (hirr : Irrational alpha)
    (f : C(AddCircle (1:ℝ), ℂ)) (hf : f ∈ Submodule.span ℂ (Set.range (@fourier 1))) :
    Tendsto (orbitAvg alpha f) atTop (𝓝 (∫ x, f x ∂haarAddCircle)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [integral_fourier]
      by_cases hk : k = 0
      · subst hk
        have h1 : orbitAvg alpha (fourier 0) =ᶠ[atTop] (fun _ => (1:ℂ)) := by
          filter_upwards [eventually_gt_atTop 0] with N hN
          have hN' : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
          simp [orbitAvg, hN']
        simpa using Tendsto.congr' h1.symm tendsto_const_nhds
      · simpa [if_neg hk, orbitAvg] using tendsto_avg_fourier hirr hk
  | zero =>
      have h : ∀ N, orbitAvg alpha 0 N = 0 := by intro N; simp [orbitAvg]
      simpa using Tendsto.congr (fun N => (h N).symm) (tendsto_const_nhds (x := (0:ℂ)))
  | add x y hx hy ihx ihy =>
      have h : ∀ N, orbitAvg alpha x N + orbitAvg alpha y N = orbitAvg alpha (x + y) N := by
        intro N; simp [orbitAvg, Finset.sum_add_distrib, mul_add]
      have hint : (∫ t, (x + y) t ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))
          = (∫ t, x t ∂(haarAddCircle : Measure (AddCircle (1:ℝ)))) + ∫ t, y t ∂haarAddCircle := by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_continuousMap x) (integrable_continuousMap y)
      rw [hint]
      exact Tendsto.congr h (ihx.add ihy)
  | smul c x hx ihx =>
      have h : ∀ N, c * orbitAvg alpha x N = orbitAvg alpha (c • x) N := by
        intro N; simp [orbitAvg, Finset.mul_sum, mul_left_comm]
      have hint : (∫ t, (c • x) t ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))
          = c * ∫ t, x t ∂(haarAddCircle : Measure (AddCircle (1:ℝ))) := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact integral_const_mul c _
      rw [hint]
      exact Tendsto.congr h (ihx.const_mul c)

