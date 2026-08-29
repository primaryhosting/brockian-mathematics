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

lemma mem_arc_iff {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (y : ℝ) :
    ((y : Circ) ∈ arc a b) ↔ Int.fract y ∈ Set.Ico a b := by
  constructor
  · rintro ⟨z, hz, hcoe⟩
    have hz01 : z ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      refine ⟨by linarith [hz.1], ?_⟩
      simpa using lt_of_lt_of_le hz.2 hb
    have hfy : Int.fract y ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg y, by simpa using Int.fract_lt_one y⟩
    have hcc : ((Int.fract y : ℝ) : Circ) = ((z : ℝ) : Circ) := by
      rw [coe_fract y, ← hcoe]
    have hz' := (AddCircle.coe_eq_coe_iff_of_mem_Ico hfy hz01).mp hcc
    rw [hz']; exact hz
  · intro h
    exact ⟨Int.fract y, h, coe_fract y⟩

