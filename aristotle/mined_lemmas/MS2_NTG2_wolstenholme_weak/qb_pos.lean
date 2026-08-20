import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma qb_pos {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) {x y : ℤ}
    (h : ¬(x = 0 ∧ y = 0)) : 0 < qb A B C x y := by
  have key := four_mul_qb A B C x y
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    have hx : x ≠ 0 := fun hx => h ⟨hx, rfl⟩
    have h2 : 0 < A * x ^ 2 := by positivity
    simpa [qb] using h2
  · have h1 : 0 < (4 * A * C - B ^ 2) * y ^ 2 := by positivity
    have h2 : 0 ≤ (2 * A * x + B * y) ^ 2 := sq_nonneg _
    nlinarith [key]

/-- Under the substitution with columns `(x₀,y₀)`, `(x₁,y₁)`, the form `qb A B C`
becomes another binary form. -/
