import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma Kset_ne_zero {δ : ℝ} {x : Fin n → ℝ} (hx : x ∈ Kset n δ) :
    x ≠ 0 := by
  rintro rfl
  simp [Kset] at hx

