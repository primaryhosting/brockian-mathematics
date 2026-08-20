import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma coprime_of_dvd_succ {r n : ℕ} (h : n ∣ r + 1) : Nat.Coprime r n := by
  have h1 : Nat.gcd r n ∣ r := Nat.gcd_dvd_left r n
  have h2 : Nat.gcd r n ∣ r + 1 := (Nat.gcd_dvd_right r n).trans h
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right h1).mpr h2)

