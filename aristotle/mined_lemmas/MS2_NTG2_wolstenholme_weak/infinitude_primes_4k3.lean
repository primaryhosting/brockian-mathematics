import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem infinitude_primes_4k3 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have h := Nat.infinite_setOf_prime_and_modEq (q := 4) (a := 3) (by norm_num) (by decide)
  refine h.mono ?_
  rintro p ⟨hp, hmod⟩
  exact ⟨hp, by simpa [Nat.ModEq] using hmod⟩

