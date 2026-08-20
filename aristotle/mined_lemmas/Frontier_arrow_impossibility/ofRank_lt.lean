import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem ofRank_lt (r : α → Nat) (hr : ∀ x y, r x = r y → x = y) (x y : α) :
    (ofRank r hr).lt x y ↔ r x < r y := Iff.rfl

end Ranking

/-! ## The rankings of three alternatives -/

/-- Score function on `Fin 3` placing `a` first, `b` second, and the remaining one last. -/
