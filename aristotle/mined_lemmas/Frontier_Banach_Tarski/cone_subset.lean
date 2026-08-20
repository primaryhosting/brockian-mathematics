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

theorem cone_subset (A : Set E) : cone A ⊆ Metric.closedBall (0 : E) 1 \ {0} := by
  rintro x ⟨hx0, hx1, -⟩
  exact ⟨by simpa [Metric.mem_closedBall] using hx1, hx0⟩

