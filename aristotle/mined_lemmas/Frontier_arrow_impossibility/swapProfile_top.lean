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


theorem swapProfile_top {a b c : Fin 3} {P : V → Ranking (Fin 3)} {j : V}
    (h : (P j).lt b a) : swapProfile a b c P j = tri b c := by
  simp [swapProfile, h]

