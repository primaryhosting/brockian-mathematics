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

theorem isParadoxical_sph : IsParadoxical SO3 sph :=
  IsParadoxical.of_equidec (Equidec.symm (equidec_sph_diff badSet_subset badSet_countable))
    isParadoxical_sph_diff_bad

end

end BT

/-
Paradoxical decompositions coming from free actions of the free group of rank two.
-/
import RequestProject.Equidec

open Set Function Pointwise

namespace BT

/-- The free group of rank two. -/
abbrev F2 := FreeGroup (Fin 2)

namespace FreeWord

variable {α : Type*} [DecidableEq α]

