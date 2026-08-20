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

theorem toWord_cancel {x : α × Bool} {w : FreeGroup α} {L : List (α × Bool)}
    (h : w.toWord = (x.1, !x.2) :: L) :
    (FreeGroup.mk [x] * w).toWord = L := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton,
    List.singleton_append, FreeGroup.reduce.cons, FreeGroup.reduce_toWord, h]
  simp

end FreeWord

/-- The set of elements of `F2` whose reduced word starts with the letter `x`. -/
