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

lemma measurableSet_arc (a b : ℝ) : MeasurableSet (arc a b) := by
  have hU : MeasurableSet (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) :=
    (isOpen_arcIoo a b).measurableSet
  have hsub : (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) ⊆ arc a b :=
    Set.image_mono Set.Ioo_subset_Ico_self
  have hfin : (arc a b \ (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ)).Finite := by
    refine Set.Finite.subset
      (Set.toFinite ({((a : ℝ) : Circ), ((b : ℝ) : Circ)} : Set Circ)) ?_
    refine subset_trans (Set.diff_subset_diff_left (Set.image_mono Set.Ico_subset_Icc_self)) ?_
    exact diff_subset_endpoints a b
  have harc : arc a b = (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ) ∪
      (arc a b \ (QuotientAddGroup.mk '' (Set.Ioo a b) : Set Circ)) := by
    rw [Set.union_diff_cancel hsub]
  rw [harc]
  exact hU.union hfin.measurableSet

