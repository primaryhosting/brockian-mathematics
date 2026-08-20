import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma data_of_dvd (n : ℕ) (M D s : ℤ) (hM : 0 < M) (hMD : (n : ℤ) * D = M + 1)
    (hdvd : M ∣ s ^ 2 + D) : ∃ u M' s' : ℤ, 0 < M' ∧ (n : ℤ) * (u * M' - s' ^ 2) - M' = 1 := by
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, M, s, hM, ?_⟩
  have h : u * M - s ^ 2 = D := by linarith [hu]
  rw [h, hMD]; ring

/-- A square root of `-D` modulo a prime `p`. -/
