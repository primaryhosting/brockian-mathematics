import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma vec3_ne_zero_iff (v : Fin 3 → ℤ) : v ≠ 0 ↔ ¬(v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := by
  constructor
  · rintro h ⟨h0, h1, h2⟩
    exact h (by funext i; fin_cases i <;> assumption)
  · intro h hv
    exact h ⟨by rw [hv]; rfl, by rw [hv]; rfl, by rw [hv]; rfl⟩

/-! ### Completing the square -/

/-- Completing the square in the first variable. -/
