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

lemma trap_eq_zero_left {u v ε x : ℝ} (hε : 0 < ε) (hx : x ≤ u) : trap u v ε x = 0 := by
  have h : (x - u) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  unfold trap
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h))

