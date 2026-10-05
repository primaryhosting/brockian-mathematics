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

lemma volume_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (volume : Measure Circ) (arc a b) = ENNReal.ofReal (b - a) := by
  have hproj := AddCircle.add_projection_respects_measure 1 0 (measurableSet_arc a b)
  rw [zero_add] at hproj
  set S : Set ℝ := QuotientAddGroup.mk ⁻¹' (arc a b) ∩ Set.Ioc 0 1 with hS
  have hmem : ∀ y : ℝ, y ∈ S ↔ (Int.fract y ∈ Set.Ico a b ∧ y ∈ Set.Ioc (0 : ℝ) 1) := by
    intro y
    simp only [hS, Set.mem_inter_iff, Set.mem_preimage]
    rw [mem_arc_iff ha hb]
  have h1 : Set.Ioo a b ⊆ S := by
    intro y hy
    rw [hmem]
    have hy0 : 0 < y := lt_of_le_of_lt ha hy.1
    have hy1 : y < 1 := lt_of_lt_of_le hy.2 hb
    refine ⟨?_, ⟨hy0, le_of_lt hy1⟩⟩
    rw [Int.fract_eq_self.mpr ⟨le_of_lt hy0, hy1⟩]
    exact ⟨le_of_lt hy.1, hy.2⟩
  have h2 : S ⊆ Set.Icc a b ∪ {(1 : ℝ)} := by
    intro y hy
    rw [hmem] at hy
    obtain ⟨hf, hy0, hy1⟩ := hy
    rcases eq_or_lt_of_le hy1 with h | h
    · right; exact h
    · left
      rw [Int.fract_eq_self.mpr ⟨le_of_lt hy0, h⟩] at hf
      exact ⟨hf.1, le_of_lt hf.2⟩
  have hle1 : ENNReal.ofReal (b - a) ≤ (volume : Measure ℝ) S := by
    have h := measure_mono (μ := (volume : Measure ℝ)) h1
    rwa [Real.volume_Ioo] at h
  have hle2 : (volume : Measure ℝ) S ≤ ENNReal.ofReal (b - a) := by
    refine le_trans (measure_mono (μ := (volume : Measure ℝ)) h2) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [Real.volume_Icc, Real.volume_singleton, add_zero]
  rw [hproj]
  exact le_antisymm hle2 hle1

