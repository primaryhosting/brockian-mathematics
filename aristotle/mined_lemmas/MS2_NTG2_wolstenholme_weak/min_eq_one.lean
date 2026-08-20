import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma min_eq_one {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm)
    (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v) (hdet : G.det = 1)
    (hmin : ∀ v : Fin 3 → ℤ, v ≠ 0 → G 0 0 ≤ Q3 G v) : G 0 0 = 1 := by
  have hapos : 0 < G 0 0 := by rw [← Q3_e0 G]; exact hpd _ e0_ne_zero
  set a := G 0 0 with hA
  set r := G 0 1 with hR
  set q := G 0 2 with hQ
  set A' := a * G 1 1 - r ^ 2 with hA'
  set B' := 2 * (a * G 1 2 - q * r) with hB'
  set C' := a * G 2 2 - q ^ 2 with hC'
  have hdisc : 4 * A' * C' - B' ^ 2 = 4 * a := by
    have := disc_complete_square hsym
    rw [hdet] at this
    rw [hA', hB', hC', hA, hR, hQ]
    linarith [this]
  -- every nonzero value of the binary form is at least `3a²/4`
  have hlow : ∀ y z : ℤ, ¬(y = 0 ∧ z = 0) → 3 * a ^ 2 ≤ 4 * qb A' B' C' y z := by
    intro y z hyz
    obtain ⟨x, hx⟩ : ∃ x : ℤ, 4 * (a * x + r * y + q * z) ^ 2 ≤ a ^ 2 := by
      set L := r * y + q * z with hL
      refine ⟨-((2 * L + a) / (2 * a)), ?_⟩
      have h2a : 0 < 2 * a := by omega
      have hr1 : 0 ≤ (2 * L + a) % (2 * a) := Int.emod_nonneg _ (by omega)
      have hr2 : (2 * L + a) % (2 * a) < 2 * a := Int.emod_lt_of_pos _ h2a
      have hdm : (2 * L + a) % (2 * a) = (2 * L + a) - (2 * a) * ((2 * L + a) / (2 * a)) :=
        Int.emod_def _ _
      have hx2 : 2 * (a * (-((2 * L + a) / (2 * a))) + L) = (2 * L + a) % (2 * a) - a := by
        linarith [hdm]
      have : a * -((2 * L + a) / (2 * a)) + r * y + q * z
          = a * (-((2 * L + a) / (2 * a))) + L := by rw [hL]; ring
      rw [this]
      nlinarith [hr1, hr2, hx2]
    have hv : (![x, y, z] : Fin 3 → ℤ) ≠ 0 := by
      rw [vec3_ne_zero_iff]
      simpa using fun _ => hyz
    have hQle := hmin _ hv
    have hcs := Q3_complete_square hsym ![x, y, z]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hcs
    rw [← hA, ← hR, ← hQ, ← hA', ← hB', ← hC'] at hcs
    nlinarith [hcs, hQle, hx, hapos]
  have hA'pos : 0 < A' := by
    have h := hlow 1 0 (by simp)
    have : qb A' B' C' 1 0 = A' := by unfold qb; ring
    rw [this] at h
    nlinarith [h, hapos]
  have hDpos : 0 < 4 * A' * C' - B' ^ 2 := by rw [hdisc]; omega
  obtain ⟨y, z, hyz, hlag⟩ := lagrange hA'pos hDpos
  have hqpos := qb_pos hA'pos hDpos hyz
  have hlow' := hlow y z hyz
  rw [hdisc] at hlag
  -- `48 q² ≥ 27 a⁴` and `48 q² ≤ 64 a` force `a = 1`
  have h1 : 27 * a ^ 4 ≤ 48 * qb A' B' C' y z ^ 2 := by
    nlinarith [hlow', hqpos, hapos,
      mul_nonneg (sub_nonneg.mpr hlow') (by positivity : (0:ℤ) ≤ 4 * qb A' B' C' y z + 3 * a ^ 2)]
  have h2 : 48 * qb A' B' C' y z ^ 2 ≤ 64 * a := by linarith [hlag]
  have h3 : 27 * a ^ 4 ≤ 64 * a := by linarith
  have hle : a ≤ 1 := by nlinarith [h3, hapos]
  omega

/-- **Every value of a positive definite integral ternary form of determinant one is a sum of
three squares.** -/
