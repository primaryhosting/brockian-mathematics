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

theorem adjugate_eq_transpose {N : Matrix (Fin 3) (Fin 3) ℝ} (hN : Nᵀ * N = 1) (hdet : N.det = 1) :
    N.adjugate = Nᵀ := by
  calc N.adjugate = (Nᵀ * N) * N.adjugate := by rw [hN, Matrix.one_mul]
    _ = Nᵀ * (N * N.adjugate) := by rw [Matrix.mul_assoc]
    _ = Nᵀ := by rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]

