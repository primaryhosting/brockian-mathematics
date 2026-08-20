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


def triR (a b x : Fin 3) : Nat := if x = a then 0 else if x = b then 1 else 2

/-- Injectivity, spelled out so that it is decidable. -/
