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

lemma grid_succ_sub {n : ℕ} (hn : 0 < n) (j : ℕ) : grid n (j + 1) - grid n j = Real.pi / n := by
  have h : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  unfold grid
  push_cast
  field_simp
  ring

/-- The step function approximating `f`, written as a combination of the indicators of the
initial segments `[0, tⱼ]`. -/
