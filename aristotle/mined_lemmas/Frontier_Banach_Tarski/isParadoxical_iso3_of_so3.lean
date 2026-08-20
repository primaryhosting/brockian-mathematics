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

theorem isParadoxical_iso3_of_so3 {A : Set E} (h : IsParadoxical SO3 A) : IsParadoxical Iso3 A :=
  IsParadoxical.map rotIso (fun g x => rotIso_smul g x) h

/-! ### Radial extension: from the sphere to the punctured ball -/

/-- The (punctured) cone over a subset of the sphere. -/
