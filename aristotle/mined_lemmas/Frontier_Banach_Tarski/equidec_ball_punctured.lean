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

theorem equidec_ball_punctured :
    Equidec Iso3 (Metric.closedBall (0 : E) 1) (Metric.closedBall (0 : E) 1 \ {0}) := by
  refine Equidec.absorb centerRot ?_ ?_
  · intro n
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show (centerRot ^ n) • (0 : E) ∈ Metric.closedBall (0 : E) 1
    rw [mem_closedBall_zero_iff, centerRot_pow_apply_zero n]
    calc ‖cVec - (rZ (n : ℝ)) • cVec‖ ≤ ‖cVec‖ + ‖(rZ (n : ℝ)) • cVec‖ := norm_sub_le _ _
      _ = 1 := by rw [norm_smul_so3, norm_cVec]; norm_num
  · intro n hn
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hmem
    rw [Set.mem_singleton_iff] at hy
    subst hy
    replace hmem : (centerRot ^ n) • (0 : E) = 0 := hmem
    rw [centerRot_pow_apply_zero n, sub_eq_zero] at hmem
    exact rZ_nat_smul_cVec_ne n hn hmem.symm

/-- **The Banach–Tarski paradox** for the closed unit ball of `ℝ³`. -/
