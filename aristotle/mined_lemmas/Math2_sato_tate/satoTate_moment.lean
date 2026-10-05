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

open MeasureTheory Real Filter Set
open scoped Topology ENNReal Nat

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The density of the Sato–Tate measure with respect to Lebesgue measure on `[0, π]`:
`θ ↦ (2/π) sin²θ`. -/

lemma satoTate_moment (k : ℕ) :
    ∫ θ, (2 * Real.cos θ) ^ k ∂satoTateMeasure =
      2 / π * 2 ^ k * (wallisCos k - wallisCos (k + 2)) := by
  rw [integral_satoTateMeasure]
  have key : (∫ θ in (0:ℝ)..π, satoTateDensity θ * (2 * Real.cos θ) ^ k)
      = ∫ θ in (0:ℝ)..π, ((2 / π * 2 ^ k) * Real.cos θ ^ k
          - (2 / π * 2 ^ k) * Real.cos θ ^ (k + 2)) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [satoTateDensity, mul_pow, Real.sin_sq]
    ring
  rw [key, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, wallisCos, wallisCos]
  ring

/-- The even moments of the Sato–Tate distribution are the Catalan numbers. -/
