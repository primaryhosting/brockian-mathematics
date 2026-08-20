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

theorem phi_injective : Function.Injective phi := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  have hne' : w.toWord ≠ [] := by
    intro h
    exact hne (FreeGroup.toWord_eq_nil_iff.mp h)
  have hcoe : (w.toWord.map letterMat).prod = 1 := by
    rw [← coe_phi_mk, FreeGroup.mk_toWord, hw]
    rfl
  exact prod_ne_one FreeGroup.isReduced_toWord hne' hcoe

end

end BT

/-
Basic theory of equidecomposability and paradoxical sets, built on Mathlib's `Equidecomp`.
-/
import Mathlib

open Set Function Pointwise

namespace BT

variable {X Y G G' : Type*}

section Defs

variable [Group G] [MulAction G X]

/-- Two sets `A B : Set X` are `G`-equidecomposable if there is an equidecomposition
of `X` (in the sense of Mathlib's `Equidecomp`) whose source is `A` and whose target is `B`. -/
