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


theorem triR_inj (a b : Fin 3) (hab : a ≠ b) : Inj3 (triR a b) := by
  revert hab; revert a b; decide

/-- Complete description of the strict preferences of `tri a b`, where `c` is the third
alternative. -/
