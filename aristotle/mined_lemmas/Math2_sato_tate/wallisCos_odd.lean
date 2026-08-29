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

lemma wallisCos_odd (n : ℕ) : wallisCos (2 * n + 1) = 0 := by
  induction n with
  | zero => simp [wallisCos]
  | succ k ih =>
      have h : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
      rw [h, wallisCos_rec, ih, mul_zero]

