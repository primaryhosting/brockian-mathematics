import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma sq_mod_prime (p : ℕ) [Fact p.Prime] (D : ℤ) (hnz : ((-D : ℤ) : ZMod p) ≠ 0)
    (hleg : legendreSym p (-D) = 1) : ∃ s : ℤ, (p : ℤ) ∣ s ^ 2 + D := by
  obtain ⟨y, hy⟩ := (legendreSym.eq_one_iff p hnz).mp hleg
  refine ⟨(y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sq, ← hy]
  push_cast
  ring

