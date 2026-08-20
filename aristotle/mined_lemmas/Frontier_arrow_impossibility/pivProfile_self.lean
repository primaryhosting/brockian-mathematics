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


theorem pivProfile_self {a b c : Fin 3} {S : List V} {i : V} {Q : V → Ranking (Fin 3)} :
    pivProfile a b c S i Q i = tri a b := by
  simp [pivProfile]

