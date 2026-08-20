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

theorem rotB_mem : rotB ∈ SO3 :=
  ⟨(Matrix.mem_unitaryGroup_iff).mpr rotB_mul_transpose, rotB_det⟩

/-- The two generating rotations, as elements of `SO(3)`. -/
