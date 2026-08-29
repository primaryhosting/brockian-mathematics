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

lemma grid_self {n : ℕ} (hn : 0 < n) : grid n n = Real.pi := by
  have h : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  unfold grid
  rw [mul_comm, mul_div_assoc, div_self h, mul_one]

