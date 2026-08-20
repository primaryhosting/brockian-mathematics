import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem sum_three_squares_int (n : ℕ) (hn : 0 < n) (h4 : ¬ (4 ∣ n)) (h8 : n % 8 ≠ 7) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ) := by
  obtain ⟨u, M, s, hM, hdet⟩ := exists_ternary_data n hn h4 h8
  have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hdet' : (Gmat (n : ℤ) u M s).det = 1 := by rw [Gmat_det]; exact hdet
  obtain ⟨x, y, z, hxyz⟩ := ternary_sum_three_squares (Gmat_isSymm (n : ℤ) u M s)
    (Gmat_posDef hnpos hM hdet) hdet' ![1, 0, 0]
  refine ⟨x, y, z, ?_⟩
  rw [← hxyz, Gmat_e0]

/-- **Legendre's three-square theorem.** -/
