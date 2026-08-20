import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma e0_ne_zero : (![1, 0, 0] : Fin 3 → ℤ) ≠ 0 := by
  intro h
  have : (![1, 0, 0] : Fin 3 → ℤ) 0 = 0 := by rw [h]; rfl
  simp at this

