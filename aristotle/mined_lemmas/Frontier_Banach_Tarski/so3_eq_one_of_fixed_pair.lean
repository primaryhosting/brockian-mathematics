/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem so3_eq_one_of_fixed_pair {N : Matrix (Fin 3) (Fin 3) ℝ} (hN : Nᵀ * N = 1)
    (hdet : N.det = 1) {u v : Fin 3 → ℝ}
    (hgram : (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 ≠ 0)
    (hu : N *ᵥ u = u) (hv : N *ᵥ v = v) : N = 1 := by
  set w := u ⨯₃ v with hw
  have hNw : N *ᵥ w = w := by
    have h := cross_mulVec N u v
    rw [hu, hv, adjugate_eq_transpose hN hdet, Matrix.transpose_transpose] at h
    exact h.symm
  set P : Matrix (Fin 3) (Fin 3) ℝ := (Matrix.of ![u, v, w])ᵀ with hP
  have hdetP : P.det ≠ 0 := by
    rw [hP, Matrix.det_transpose, hw, det_triple]
    exact hgram
  have hmul : ∀ (z : Fin 3 → ℝ), N *ᵥ z = z → ∀ i, ∑ k, N i k * z k = z i := by
    intro z hz i
    have := congrFun hz i
    simpa [Matrix.mulVec, dotProduct] using this
  have hNP : N * P = P := by
    ext i j
    fin_cases j <;>
      simp only [Matrix.mul_apply, hP, Matrix.transpose_apply, Matrix.of_apply]
    · simpa using hmul u hu i
    · simpa using hmul v hv i
    · simpa using hmul w hNw i
  have hPunit : IsUnit P.det := isUnit_iff_ne_zero.mpr hdetP
  calc N = N * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv P hPunit, Matrix.mul_one]
    _ = (N * P) * P⁻¹ := by rw [Matrix.mul_assoc]
    _ = P * P⁻¹ := by rw [hNP]
    _ = 1 := Matrix.mul_nonsing_inv P hPunit

/-- Two distinct, non-antipodal unit vectors have nondegenerate Gram determinant. -/
