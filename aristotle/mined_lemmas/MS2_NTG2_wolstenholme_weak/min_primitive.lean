import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma min_primitive {G : Matrix (Fin 3) (Fin 3) ℤ} (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v)
    {w : Fin 3 → ℤ} (hw0 : w ≠ 0) (hmin : ∀ v : Fin 3 → ℤ, v ≠ 0 → Q3 G w ≤ Q3 G v) :
    Int.gcd ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) (w 2) = 1 := by
  set d : ℕ := Int.gcd ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) (w 2) with hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [hd] at h
    have h1 : ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) = 0 ∧ w 2 = 0 := Int.gcd_eq_zero_iff.mp h
    have h2 : Int.gcd (w 0) (w 1) = 0 := by exact_mod_cast h1.1
    have h3 := Int.gcd_eq_zero_iff.mp h2
    exact hw0 (by funext i; fin_cases i <;> simp [h3.1, h3.2, h1.2])
  have hd1 : (d : ℤ) ∣ ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) := Int.gcd_dvd_left _ _
  have hdvd : ∀ i, (d : ℤ) ∣ w i := by
    intro i
    fin_cases i
    · exact hd1.trans (Int.gcd_dvd_left (w 0) (w 1))
    · exact hd1.trans (Int.gcd_dvd_right (w 0) (w 1))
    · exact Int.gcd_dvd_right _ _
  set w' : Fin 3 → ℤ := fun i => w i / (d : ℤ) with hw'
  have hww' : w = fun i => (d : ℤ) * w' i := by
    funext i
    rw [hw']
    exact (Int.mul_ediv_cancel' (hdvd i)).symm
  have hw'0 : w' ≠ 0 := by
    intro h
    apply hw0
    rw [hww', h]
    funext i
    simp
  have hQ : Q3 G w = (d : ℤ) ^ 2 * Q3 G w' := by
    conv_lhs => rw [hww']
    exact Q3_smul G (d : ℤ) w'
  have h1 : Q3 G w ≤ Q3 G w' := hmin w' hw'0
  have hpos : 0 < Q3 G w' := hpd w' hw'0
  have hdge : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
  have hkey : ((d : ℤ) ^ 2 - 1) * Q3 G w' ≤ 0 := by nlinarith [hQ, h1]
  have hd2 : (d : ℤ) ^ 2 ≤ 1 := by nlinarith [hkey, hpos]
  have hdle : (d : ℤ) ≤ 1 := by nlinarith [hd2, hdge]
  omega

/-! ### The main theorem -/

