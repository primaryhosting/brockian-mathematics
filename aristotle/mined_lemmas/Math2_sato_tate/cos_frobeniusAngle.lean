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

open scoped Real ENNReal NNReal Classical
open MeasureTheory Filter Topology Set

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma cos_frobeniusAngle {a : ℤ} {p : ℕ} (hp : 0 < p)
    (hasse : |(a : ℝ)| ≤ 2 * Real.sqrt p) :
    2 * Real.sqrt p * Real.cos (frobeniusAngle a p) = (a : ℝ) := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
  have h2 : (0:ℝ) < 2 * Real.sqrt p := by linarith
  have habs : |(a:ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
    rw [abs_div, abs_of_pos h2, div_le_one h2]; exact hasse
  rw [abs_le] at habs
  rw [frobeniusAngle, Real.cos_arccos habs.1 habs.2]
  field_simp

/-- The empirical distribution of the first `N` terms of a sequence of angles. -/
