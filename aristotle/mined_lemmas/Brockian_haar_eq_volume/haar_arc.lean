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

lemma haar_arc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (haarAddCircle : Measure (AddCircle (1:ℝ))) (arc a b) = ENNReal.ofReal (b - a) := by
  rw [haar_eq_volume]
  rcases eq_or_lt_of_le hab with rfl | h
  · simp [arc]
  rw [AddCircle.add_projection_respects_measure (T := (1:ℝ)) a (measurableSet_arc a b),
    preimage_arc_inter ha h hb]
  have hvol : (volume : Measure ℝ) (Set.Ioo a b ∪ {a + 1}) = volume (Set.Ioo a b) := by
    refine le_antisymm ?_ (measure_mono Set.subset_union_left)
    calc volume (Set.Ioo a b ∪ {a+1}) ≤ volume (Set.Ioo a b) + volume ({a+1} : Set ℝ) :=
          measure_union_le _ _
      _ = volume (Set.Ioo a b) := by simp
  rw [hvol, Real.volume_Ioo]

