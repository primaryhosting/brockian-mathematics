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

lemma satoTate_moment_odd (n : ℕ) :
    ∫ θ, (2 * Real.cos θ) ^ (2 * n + 1) ∂satoTateMeasure = 0 := by
  have h : 2 * n + 1 + 2 = 2 * (n + 1) + 1 := by ring
  rw [satoTate_moment, wallisCos_odd, h, wallisCos_odd]
  ring

/-! ## Frobenius angles -/

