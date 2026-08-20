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

theorem badSet_countable : badSet.Countable := by
  have hsub : badSet ⊆ ⋃ w : F2, {x ∈ sph | w ≠ 1 ∧ phi w • x = x} := by
    rintro x ⟨hx, w, hw, hwx⟩
    exact Set.mem_iUnion.2 ⟨w, hx, hw, hwx⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun w => ?_)
  by_cases hw : w = 1
  · have : {x ∈ sph | w ≠ 1 ∧ phi w • x = x} = ∅ := by
      ext x; simp [hw]
    rw [this]; exact Set.countable_empty
  · have hne : phi w ≠ 1 := fun h => hw (phi_injective (by rw [h, map_one]))
    refine Set.Countable.mono ?_ (fixed_countable (phi w) hne)
    rintro x ⟨hx, -, hwx⟩
    exact ⟨hx, hwx⟩

