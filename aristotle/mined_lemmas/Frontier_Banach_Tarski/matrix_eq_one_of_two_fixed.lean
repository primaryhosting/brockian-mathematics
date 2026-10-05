import RequestProject.Equidecomp

/-!
# Rotations of `ℝ³`

Set-up for the Banach–Tarski paradox: the group `SO(3)` of rotations acting on
`E = EuclideanSpace ℝ (Fin 3)`, the group of isometries of `E`, and the fact that a
non-identity rotation fixes at most two points of the unit sphere.
-/

open Matrix

namespace BanachTarski

/-- Three dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of rotations of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

noncomputable instance : SMul ↥SO3 E :=
  ⟨fun M x => WithLp.toLp 2 ((M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x)⟩


theorem matrix_eq_one_of_two_fixed {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hMt' : M * Mᵀ = 1) (hdet : M.det = 1) {p q : Fin 3 → ℝ} (hp : p ⬝ᵥ p = 1) (hq : q ⬝ᵥ q = 1)
    (hpq : (p ⬝ᵥ q) ^ 2 ≠ 1) (hMp : M *ᵥ p = p) (hMq : M *ᵥ q = q) : M = 1 := by
  set u := p ⨯₃ q with hu
  have hMu : M *ᵥ u = u := by
    have h1 : Mᵀ *ᵥ u = u := by
      have := transpose_mulVec_cross M p q
      rw [hMp, hMq, hdet, one_smul] at this
      exact this
    calc M *ᵥ u = M *ᵥ (Mᵀ *ᵥ u) := by rw [h1]
      _ = (M * Mᵀ) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = u := by rw [hMt', Matrix.one_mulVec]
  have huu : u ⬝ᵥ u = 1 - (p ⬝ᵥ q) ^ 2 := by
    rw [hu, cross_dot_self, hp, hq]; ring
  have hune : u ⬝ᵥ u ≠ 0 := by
    rw [huu]
    intro h
    exact hpq (by linarith)
  set N : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![u, p, q] with hN
  have hdetN : N.det ≠ 0 := by
    rw [hN, det_of_three]
    exact hune
  have hrows : ∀ i, M *ᵥ (N i) = N i := by
    intro i
    fin_cases i
    · exact hMu
    · exact hMp
    · exact hMq
  have hNM : N * Mᵀ = N := by
    ext i j
    have := congrFun (hrows i) j
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have : N⁻¹ * (N * Mᵀ) = N⁻¹ * N := by rw [hNM]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N (by simpa using hdetN), Matrix.one_mul] at this
  have hMT : Mᵀ = 1 := this
  have : M = Mᵀᵀ := (Matrix.transpose_transpose M).symm
  rw [this, hMT, Matrix.transpose_one]

/-- Two unit vectors whose inner product has absolute value one are equal up to sign. -/
