/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real ENNReal NNReal Classical
open MeasureTheory Filter Topology Set

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma satoTate_value_nonneg {a b : ℝ} (hab : a ≤ b) :
    0 ≤ (b - a - (Real.sin b * Real.cos b - Real.sin a * Real.cos a)) / Real.pi := by
  have h : (0:ℝ) ≤ ∫ x in a..b, Real.sin x ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  rw [integral_sin_sq] at h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  apply div_nonneg _ hpi.le
  linarith

/-- The Sato–Tate measure of a subinterval `[a,b] ⊆ [0,π]`. -/
