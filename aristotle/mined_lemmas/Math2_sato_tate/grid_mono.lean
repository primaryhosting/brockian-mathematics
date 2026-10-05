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

lemma grid_mono {n : ℕ} {i j : ℕ} (h : i ≤ j) : grid n i ≤ grid n j := by
  unfold grid
  have hij : (i : ℝ) ≤ j := Nat.cast_le.2 h
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpi := Real.pi_pos.le
  gcongr

