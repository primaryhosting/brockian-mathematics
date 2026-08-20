import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma exists_unimodular_col {w : Fin 3 → ℤ}
    (hw : Int.gcd ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) (w 2) = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ U *ᵥ ![1, 0, 0] = w := by
  have key : ∃ V : Matrix (Fin 3) (Fin 3) ℤ, V.det = 1 ∧ V *ᵥ w = ![1, 0, 0] := by
    set g : ℤ := ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) with hg
    by_cases hg0 : g = 0
    · -- `w 0 = w 1 = 0` and `w 2 = ±1`
      have h01 : w 0 = 0 ∧ w 1 = 0 := by
        have hcast : ((Int.gcd (w 0) (w 1) : ℕ) : ℤ) = 0 := by rw [← hg]; exact hg0
        have : Int.gcd (w 0) (w 1) = 0 := by exact_mod_cast hcast
        exact Int.gcd_eq_zero_iff.mp this
      have hw2 : w 2 = 1 ∨ w 2 = -1 := by
        rw [hg0] at hw
        have : (w 2).natAbs = 1 := by simpa [Int.gcd] using hw
        omega
      rcases hw2 with h2 | h2
      · refine ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three], ?_⟩
        funext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h01.1, h01.2, h2]
      · refine ⟨!![0, 0, -1; -1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three], ?_⟩
        funext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h01.1, h01.2, h2]
    · -- the generic case
      have hdvd0 : g ∣ w 0 := by rw [hg]; exact Int.gcd_dvd_left (w 0) (w 1)
      have hdvd1 : g ∣ w 1 := by rw [hg]; exact Int.gcd_dvd_right (w 0) (w 1)
      obtain ⟨s, hs⟩ := hdvd0
      obtain ⟨t, ht⟩ := hdvd1
      set a : ℤ := Int.gcdA (w 0) (w 1) with ha
      set b : ℤ := Int.gcdB (w 0) (w 1) with hb
      have hbez : g = w 0 * a + w 1 * b := by rw [hg, ha, hb]; exact Int.gcd_eq_gcd_ab _ _
      have hst : a * s + b * t = 1 := by
        have : g * 1 = g * (a * s + b * t) := by
          rw [mul_one]
          nth_rewrite 1 [hbez]
          rw [hs, ht]; ring
        exact (mul_left_cancel₀ hg0 this).symm
      set a' : ℤ := Int.gcdA g (w 2) with ha'
      set b' : ℤ := Int.gcdB g (w 2) with hb'
      have hbez' : (1 : ℤ) = g * a' + w 2 * b' := by
        have := Int.gcd_eq_gcd_ab g (w 2)
        rw [hw] at this
        simpa [ha', hb'] using this
      refine ⟨(!![a', 0, b'; 0, 1, 0; -w 2, 0, g] : Matrix (Fin 3) (Fin 3) ℤ) *
        !![a, b, 0; -t, s, 0; 0, 0, 1], ?_, ?_⟩
      · rw [Matrix.det_mul]
        simp only [Matrix.det_fin_three]
        simp
        nlinarith [hbez', hst]
      · rw [← Matrix.mulVec_mulVec]
        have h1 : (!![a, b, 0; -t, s, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ w
            = ![g, 0, w 2] := by
          funext i
          fin_cases i <;>
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
          · linarith [hbez]
          · rw [hs, ht]; ring
        rw [h1]
        funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · linarith [hbez']
        · ring
  obtain ⟨V, hVdet, hVw⟩ := key
  refine ⟨V.adjugate, ?_, ?_⟩
  · rw [Matrix.det_adjugate, hVdet]; simp
  · have hinv : V.adjugate * V = 1 := by rw [Matrix.adjugate_mul, hVdet]; simp
    calc V.adjugate *ᵥ ![1, 0, 0] = V.adjugate *ᵥ (V *ᵥ w) := by rw [hVw]
      _ = (V.adjugate * V) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = w := by rw [hinv, Matrix.one_mulVec]

/-! ### The minimum of a positive definite form -/

