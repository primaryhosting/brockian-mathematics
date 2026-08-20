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

theorem exists_not_mem_of_countable {S : Set ℝ} (hS : S.Countable) : ∃ t : ℝ, t ∉ S := by
  by_contra hcon
  push_neg at hcon
  exact Cardinal.not_countable_real (Set.Countable.mono (fun x _ => hcon x) hS)

/-! ### Finding an absorbing rotation -/

/-- There is an angle whose rotation about the `z`-axis moves a countable set off itself,
provided the set avoids the poles. -/
