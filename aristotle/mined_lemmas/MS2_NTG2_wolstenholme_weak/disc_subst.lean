import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma disc_subst (A B C x₀ y₀ x₁ y₁ : ℤ) :
    4 * qb A B C x₀ y₀ * qb A B C x₁ y₁ -
        (2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁) ^ 2 =
      (4 * A * C - B ^ 2) * (x₀ * y₁ - x₁ * y₀) ^ 2 := by
  unfold qb; ring

