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

theorem letterMat_mulVec (x : Fin 2 × Bool) (u : ℤ × ℤ × ℤ) :
    letterMat x *ᵥ vecR u = ((3 : ℝ)⁻¹) • vecR (step x u) := by
  funext i
  rcases fin2_cases x.1 with hx | hx <;> cases hb : x.2 <;>
    fin_cases i <;>
      simp [letterMat, step, sgn, hx, hb, rotA, rotB, vecR, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.transpose_apply]
  all_goals ring_nf
  all_goals (try rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])
  all_goals (try ring)

/-- The mod-3 invariant satisfied by the state of a reduced word. -/
