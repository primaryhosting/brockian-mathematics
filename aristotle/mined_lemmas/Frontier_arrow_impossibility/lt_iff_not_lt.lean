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


theorem lt_iff_not_lt {x y : α} (hxy : x ≠ y) : R.lt y x ↔ ¬ R.lt x y :=
  ⟨fun h hc => R.asym h hc, fun h => (R.tot x y hxy).resolve_left h⟩

/-- The ranking induced by an injective "score" function into `Nat` (smaller is better). -/
