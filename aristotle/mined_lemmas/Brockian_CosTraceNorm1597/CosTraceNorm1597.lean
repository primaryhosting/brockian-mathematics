import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian

open Matrix

/-- The planar rotation matrix by angle `θ`. -/

theorem CosTraceNorm1597 (θ : ℝ) :
    (rot θ)ᵀ * rot θ = 1 ∧ (rot θ).trace = 2 * Real.cos θ ∧
      |(rot θ).trace| ≤ 2 ∧ (|(rot θ).trace| = 2 ↔ Real.cos θ = 1 ∨ Real.cos θ = -1) := by
  refine ⟨rot_orthogonal θ, trace_rot θ, ?_, ?_⟩
  · have := abs_trace_le_card_of_orthogonal (rot θ) (rot_orthogonal θ)
    simpa using this
  · rw [trace_rot, abs_mul]
    constructor
    · intro h
      have : |Real.cos θ| = 1 := by
        rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
        linarith
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (h | h) <;> simp [h]

end Brockian

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

