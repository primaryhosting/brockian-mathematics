import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem nat_sum_three_squares (n : ℕ) (h : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, by norm_num⟩
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      have hmpos : 0 < m := by omega
      have hlt : m < 4 * m := by omega
      have h' : ¬ ∃ a b : ℕ, m = 4 ^ a * (8 * b + 7) := by
        rintro ⟨a, b, rfl⟩
        exact h ⟨a + 1, b, by ring⟩
      obtain ⟨x, y, z, hxyz⟩ := ih m hlt h'
      exact ⟨2 * x, 2 * y, 2 * z, by rw [← hxyz]; ring⟩
    · have h8 : n % 8 ≠ 7 := by
        intro he
        exact h ⟨0, n / 8, by omega⟩
      obtain ⟨x, y, z, hxyz⟩ := sum_three_squares_int n hn h4 h8
      refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_⟩
      have : ((x.natAbs : ℤ)) ^ 2 + ((y.natAbs : ℤ)) ^ 2 + ((z.natAbs : ℤ)) ^ 2 = (n : ℤ) := by
        rw [Int.natAbs_sq, Int.natAbs_sq, Int.natAbs_sq]
        exact hxyz
      exact_mod_cast this

end ThreeSquares

