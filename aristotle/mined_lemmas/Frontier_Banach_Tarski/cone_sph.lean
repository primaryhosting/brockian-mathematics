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

theorem cone_sph : cone sph = Metric.closedBall (0 : E) 1 \ {0} := by
  ext x
  constructor
  · exact fun hx => cone_subset sph hx
  · rintro ⟨hx1, hx0⟩
    have hx0' : x ≠ 0 := hx0
    have hn : ‖x‖ ≠ 0 := fun h => hx0' (norm_eq_zero.mp h)
    refine ⟨hx0', by simpa [Metric.mem_closedBall] using hx1, ?_⟩
    show ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

