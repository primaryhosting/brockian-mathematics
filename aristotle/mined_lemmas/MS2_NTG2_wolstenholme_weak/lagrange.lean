import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem lagrange {A B C : ℤ} (hA : 0 < A) (hD : 0 < 4 * A * C - B ^ 2) :
    ∃ x y : ℤ, ¬(x = 0 ∧ y = 0) ∧ 3 * qb A B C x y ^ 2 ≤ 4 * A * C - B ^ 2 := by
  obtain ⟨x₀, y₀, hne0, hmin⟩ := exists_min_qb hA hD
  obtain ⟨x₁, y₁, hdet, hB, hC⟩ := reduction hA hD hne0 hmin
  refine ⟨x₀, y₀, hne0, ?_⟩
  have key := disc_subst A B C x₀ y₀ x₁ y₁
  rw [hdet] at key
  have hmpos : 0 < qb A B C x₀ y₀ := qb_pos hA hD hne0
  nlinarith [key, hB, hC, hmpos]

/-- A positive definite integral binary quadratic form with `4AC - B² = 4` is
a sum of two squares of integral linear forms. -/
