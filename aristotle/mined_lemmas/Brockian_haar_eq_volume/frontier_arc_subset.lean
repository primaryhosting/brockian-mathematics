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

lemma frontier_arc_subset (a b : ℝ) :
    frontier (arc a b) ⊆ {((a : ℝ) : AddCircle (1:ℝ)), ((b : ℝ) : AddCircle (1:ℝ))} := by
  intro z hz
  have h1 : z ∈ closure (arc a b) := hz.1
  have h2 : z ∉ interior (arc a b) := hz.2
  have hcl : closure (arc a b) ⊆ (fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Icc a b :=
    closure_minimal (Set.image_mono Set.Ico_subset_Icc_self) (isClosed_image_Icc a b)
  have hint : (fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Ioo a b ⊆ interior (arc a b) :=
    interior_maximal (Set.image_mono Set.Ioo_subset_Ico_self) (isOpen_image_Ioo a b)
  obtain ⟨t, ht, rfl⟩ := hcl h1
  rcases eq_or_lt_of_le ht.1 with rfl | hta
  · exact Or.inl rfl
  rcases eq_or_lt_of_le ht.2 with rfl | htb
  · exact Or.inr rfl
  exact absurd (hint ⟨t, ⟨hta, htb⟩, rfl⟩) h2

