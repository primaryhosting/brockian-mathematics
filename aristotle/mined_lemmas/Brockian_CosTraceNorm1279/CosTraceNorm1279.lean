/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian

/-- The planar rotation matrix by angle `θ`. -/

theorem CosTraceNorm1279 (θ : ℝ) (n : ℕ) :
    Matrix.trace ((rot θ) ^ n) = 2 * Real.cos (n * θ) ∧
    |Matrix.trace ((rot θ) ^ n)| ≤ 2 ∧
    (|Matrix.trace ((rot θ) ^ n)| = 2 ↔ Real.sin (n * θ) = 0) ∧
    (Real.sin (n * θ) ≠ 0 → |Matrix.trace ((rot θ) ^ n)| < 2) := by
  have htr : Matrix.trace ((rot θ) ^ n) = 2 * Real.cos (n * θ) := trace_rot_pow θ n
  have habs : |Matrix.trace ((rot θ) ^ n)| = 2 * |Real.cos (n * θ)| := by
    rw [htr, abs_mul]
    norm_num
  have hle : |Real.cos ((n : ℝ) * θ)| ≤ 1 := Real.abs_cos_le_one _
  refine ⟨htr, ?_, ?_, ?_⟩
  · rw [habs]; linarith
  · rw [habs]
    constructor
    · intro h
      exact (abs_cos_eq_one_iff _).mp (by linarith)
    · intro h
      rw [(abs_cos_eq_one_iff _).mpr h]
      norm_num
  · intro h
    rw [habs]
    rcases lt_or_eq_of_le hle with hlt | heq
    · linarith
    · exact absurd ((abs_cos_eq_one_iff _).mp heq) h

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

