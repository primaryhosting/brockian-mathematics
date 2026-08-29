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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: this Lean toolchain requires `import` to be the very first command in a file, so the
required header comment appears immediately after the import.)
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Real BigOperators

namespace Brockian.Equidistribution

/-- The circle `ℝ / ℤ`, on which we study equidistribution. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

noncomputable instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨by simp⟩

/-- Continuous functions on the (compact) circle are integrable for any finite measure. -/

lemma volume_frontier_arc (a b : ℝ) :
    (volume : Measure Circ) (frontier (arc a b)) = 0 := by
  have hclosure : closure (arc a b) ⊆ (QuotientAddGroup.mk '' (Set.Icc a b) : Set Circ) :=
    closure_minimal (Set.image_mono Set.Ico_subset_Icc_self) (isClosed_arcIcc a b)
  have hint : (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) ⊆ interior (arc a b) :=
    interior_maximal (Set.image_mono Set.Ioo_subset_Ico_self) (isOpen_arcIoo a b)
  have hsub : frontier (arc a b) ⊆ {((a : ℝ) : Circ), ((b : ℝ) : Circ)} :=
    subset_trans (Set.diff_subset_diff hclosure hint) (diff_subset_endpoints a b)
  refine measure_mono_null hsub ?_
  rw [Set.insert_eq]
  exact measure_union_null (volume_singleton_circ _) (volume_singleton_circ _)

/-! ### The main theorem -/

/-- **Weyl's equidistribution theorem.**  If a real sequence `x` has the asymptotic property that
all its nontrivial exponential averages `(1/N) ∑_{n < N} e(h xₙ)` tend to `0`, then `x` is
equidistributed modulo one: for every subinterval `[a, b) ⊆ [0, 1]` the proportion of the first `N`
fractional parts lying in `[a, b)` tends to its length `b - a`. -/
