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

theorem rotA_mem : rotA ∈ SO3 :=
  ⟨(Matrix.mem_unitaryGroup_iff).mpr rotA_mul_transpose, rotA_det⟩

