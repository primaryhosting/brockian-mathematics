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

def Inv (L : List (Fin 2 × Bool)) : Prop :=
  ¬ ((3 : ℤ) ∣ (stateOf L).2.1) ∧
  (∀ e : Bool, L.head? = some (0, e) →
      ((stateOf L).1 + sgn e * (stateOf L).2.1) % 3 = 0 ∧ (stateOf L).2.2 % 3 = 0) ∧
  (∀ e : Bool, L.head? = some (1, e) →
      (stateOf L).1 % 3 = 0 ∧ ((stateOf L).2.2 - sgn e * (stateOf L).2.1) % 3 = 0) ∧
  (L = [] → (stateOf L).1 % 3 = 0 ∧ (stateOf L).2.2 % 3 = 0)

