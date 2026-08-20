import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem ternary_sum_three_squares {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm)
    (hpd : ∀ v : Fin 3 → ℤ, v ≠ 0 → 0 < Q3 G v) (hdet : G.det = 1) (v : Fin 3 → ℤ) :
    ∃ x y z : ℤ, Q3 G v = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨w, hw0, hwmin⟩ := exists_min_Q3 hpd
  obtain ⟨U, hUdet, hUw⟩ := exists_unimodular_col (min_primitive hpd hw0 hwmin)
  have hUinv : U.adjugate * U = 1 := by rw [Matrix.adjugate_mul, hUdet]; simp
  have hUinj : ∀ x : Fin 3 → ℤ, x ≠ 0 → U *ᵥ x ≠ 0 := by
    intro x hx hUx
    apply hx
    calc x = (U.adjugate * U) *ᵥ x := by rw [hUinv, Matrix.one_mulVec]
      _ = U.adjugate *ᵥ (U *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hUx, Matrix.mulVec_zero]
  set G' := Uᵀ * G * U with hG'
  have hsym' : G'.IsSymm := isSymm_congr hsym U
  have hdet' : G'.det = 1 := by rw [hG', det_congr, hUdet, hdet]; ring
  have hpd' : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < Q3 G' x := by
    intro x hx
    rw [hG', Q3_congr]
    exact hpd _ (hUinj x hx)
  have hmin' : ∀ x : Fin 3 → ℤ, x ≠ 0 → G' 0 0 ≤ Q3 G' x := by
    intro x hx
    rw [← Q3_e0 G', hG', Q3_congr, Q3_congr, hUw]
    exact hwmin _ (hUinj x hx)
  have ha1 : G' 0 0 = 1 := min_eq_one hsym' hpd' hdet' hmin'
  -- complete the square in the new basis
  set r := G' 0 1 with hR
  set q := G' 0 2 with hQ
  set A' := G' 1 1 - r ^ 2 with hA'
  set B' := 2 * (G' 1 2 - q * r) with hB'
  set C' := G' 2 2 - q ^ 2 with hC'
  have hcsq : ∀ x : Fin 3 → ℤ,
      Q3 G' x = (x 0 + r * x 1 + q * x 2) ^ 2 + qb A' B' C' (x 1) (x 2) := by
    intro x
    have h := Q3_complete_square hsym' x
    rw [ha1] at h
    rw [hA', hB', hC']
    unfold qb at h ⊢
    linear_combination h
  have hdisc : 4 * A' * C' - B' ^ 2 = 4 := by
    have h := disc_complete_square hsym'
    rw [hdet', ha1] at h
    rw [hA', hB', hC']
    linear_combination h
  have hA'pos : 0 < A' := by
    have hv : (![-r, 1, 0] : Fin 3 → ℤ) ≠ 0 := by
      rw [vec3_ne_zero_iff]; simp
    have hval : Q3 G' ![-r, 1, 0] = A' := by
      rw [hcsq]
      simp [qb]
    have hpos := hpd' _ hv
    rwa [hval] at hpos
  obtain ⟨p₁, p₂, p₃, p₄, hqb⟩ := binary_det_one hA'pos hdisc
  -- transport back
  set v' := U.adjugate *ᵥ v with hv'
  have hUv' : U *ᵥ v' = v := by
    rw [hv', Matrix.mulVec_mulVec, Matrix.mul_adjugate, hUdet]
    simp
  refine ⟨v' 0 + r * v' 1 + q * v' 2, p₁ * v' 1 + p₂ * v' 2, p₃ * v' 1 + p₄ * v' 2, ?_⟩
  have hGG : Q3 G v = Q3 G' v' := by rw [hG', Q3_congr, hUv']
  rw [hGG, hcsq v', hqb]
  ring

end ThreeSquares

import NTGaps2.TernaryForm
import NTGaps2.Construction

/-!
# The three-square theorem of Legendre and Gauss

Combining the arithmetic construction of `NTGaps2/Construction.lean` with the reduction theory
of `NTGaps2/TernaryForm.lean` we prove that every natural number which is not of the form
`4^a (8b+7)` is a sum of three squares.
-/

namespace ThreeSquares

open Matrix

/-- The candidate Gram matrix `!![n, 1, 0; 1, u, -s; 0, -s, M]`. -/
