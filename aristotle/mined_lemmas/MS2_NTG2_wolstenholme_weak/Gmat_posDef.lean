import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Gmat_posDef {n u M s : ℤ} (hn : 0 < n) (hM : 0 < M)
    (hdet : n * (u * M - s ^ 2) - M = 1) :
    ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 (Gmat n u M s) v := by
  have hdet' : (Gmat n u M s).det = 1 := by rw [Gmat_det]; exact hdet
  have hsym := Gmat_isSymm n u M s
  set A' := n * u - 1 ^ 2 with hA'
  set B' := 2 * (n * -s - 0 * 1) with hB'
  set C' := n * M - 0 ^ 2 with hC'
  have hdisc : 4 * A' * C' - B' ^ 2 = 4 * n := by
    have h := disc_complete_square hsym
    rw [hdet'] at h
    simp only [Gmat_00, Gmat_01, Gmat_02, Gmat_11, Gmat_12, Gmat_22] at h
    rw [hA', hB', hC']
    linear_combination h
  have hCpos : 0 < C' := by rw [hC']; nlinarith [mul_pos hn hM]
  have hA'pos : 0 < A' := by
    rcases lt_trichotomy A' 0 with h | h | h
    · nlinarith [hdisc, hCpos, sq_nonneg B', hn]
    · rw [h] at hdisc; nlinarith [hdisc, sq_nonneg B', hn]
    · exact h
  have hDpos : 0 < 4 * A' * C' - B' ^ 2 := by rw [hdisc]; omega
  intro v hv
  have hcs := Q3_complete_square hsym v
  simp only [Gmat_00, Gmat_01, Gmat_02, Gmat_11, Gmat_12, Gmat_22] at hcs
  rw [← hA', ← hB', ← hC'] at hcs
  rw [vec3_ne_zero_iff] at hv
  by_cases h12 : v 1 = 0 ∧ v 2 = 0
  · have hv0 : v 0 ≠ 0 := by tauto
    have hqb0 : qb A' B' C' (v 1) (v 2) = 0 := by rw [h12.1, h12.2]; unfold qb; ring
    rw [hqb0, h12.1, h12.2] at hcs
    have hne : n * v 0 + 1 * 0 + 0 * 0 ≠ 0 := by
      simpa using mul_ne_zero (by omega) hv0
    have h1 : 0 < (n * v 0 + 1 * 0 + 0 * 0) ^ 2 := pow_two_pos_of_ne_zero hne
    nlinarith [hcs, h1, hn]
  · have hqbpos : 0 < qb A' B' C' (v 1) (v 2) := qb_pos hA'pos hDpos h12
    nlinarith [hcs, hqbpos, sq_nonneg (n * v 0 + 1 * v 1 + 0 * v 2), hn]

/-- The three-square theorem, integral version, for `n` not divisible by `4` and not `7` mod `8`. -/
