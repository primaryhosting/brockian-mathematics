import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma qb_subst (A B C x₀ y₀ x₁ y₁ s t : ℤ) :
    qb A B C (x₀ * s + x₁ * t) (y₀ * s + y₁ * t) =
      qb (qb A B C x₀ y₀) (2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁)
        (qb A B C x₁ y₁) s t := by
  unfold qb; ring

/-- The discriminant is a unimodular invariant. -/
