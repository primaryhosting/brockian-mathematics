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

lemma orbitAvg_dist (alpha : ℝ) (f g : C(AddCircle (1:ℝ), ℂ)) (N : ℕ) :
    dist (orbitAvg alpha f N) (orbitAvg alpha g N) ≤ ‖f - g‖ := by
  rw [dist_eq_norm, orbitAvg, orbitAvg, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv,
    Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [norm_nonneg]
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hbound : ‖∑ n ∈ Finset.range N, (f (orbitPoint alpha n) - g (orbitPoint alpha n))‖
      ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ Finset.range N, (f (orbitPoint alpha n) - g (orbitPoint alpha n))‖
        ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ := by
          refine norm_sum_le_of_le _ (fun i _ => ?_)
          simpa using ContinuousMap.norm_coe_le_norm (f - g) (orbitPoint alpha i)
      _ = N * ‖f - g‖ := by simp
  calc (N:ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, (f (orbitPoint alpha n) - g (orbitPoint alpha n))‖
      ≤ (N:ℝ)⁻¹ * (N * ‖f - g‖) := by gcongr
    _ = ‖f - g‖ := by field_simp

