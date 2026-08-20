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


theorem bTop_not_mem {a b c : Fin 3} {S : List V} {j : V} (h : j ∉ S) :
    bTop a b c S j = tri a c := by
  simp [bTop, h]

open Classical in
/-- From a profile in which `b` is extremal for every voter, the profile obtained by
keeping `b`'s position and ranking `c` above `a`. -/
