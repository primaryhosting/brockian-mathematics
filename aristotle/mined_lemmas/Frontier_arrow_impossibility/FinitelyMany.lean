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


def FinitelyMany (V : Type v) : Prop := ∃ l : List V, ∀ x : V, x ∈ l

/-- Since preferences are rankings, agreement on `x < y` alone already gives the full
hypothesis of IIA for the pair `{x, y}`. -/
