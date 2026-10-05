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

lemma integral_density_mul_nonneg {u v : ℝ} (huv : u ≤ v) {φ : ℝ → ℝ}
    (hφ0 : ∀ x, 0 ≤ φ x) : 0 ≤ ∫ x in u..v, satoTateDensity x * φ x :=
  intervalIntegral.integral_nonneg huv fun x _ =>
    mul_nonneg (satoTateDensity_nonneg x) (hφ0 x)

