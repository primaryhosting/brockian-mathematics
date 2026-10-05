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

lemma trap_eq_one {u v ε x : ℝ} (hε : 0 < ε) (h1 : u + ε ≤ x) (h2 : x ≤ v - ε) :
    trap u v ε x = 1 := by
  have ha : (1 : ℝ) ≤ (x - u) / ε := by rw [le_div_iff₀ hε]; linarith
  have hb : (1 : ℝ) ≤ (v - x) / ε := by rw [le_div_iff₀ hε]; linarith
  unfold trap
  rw [min_eq_left (le_min ha hb), max_eq_right zero_le_one]

/-! ### Comparison of the smoothed integrals with the mass of an interval -/

