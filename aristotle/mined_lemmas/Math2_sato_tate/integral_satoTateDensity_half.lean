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

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma integral_satoTateDensity_half : ∫ x in (0 : ℝ)..(Real.pi / 2), satoTateDensity x = 1 / 2 := by
  have hp := Real.pi_pos
  unfold satoTateDensity
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  simp
  field_simp

