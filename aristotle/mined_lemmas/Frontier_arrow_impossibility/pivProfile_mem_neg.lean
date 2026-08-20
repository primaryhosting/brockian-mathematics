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


theorem pivProfile_mem_neg {a b c : Fin 3} {S : List V} {i j : V} {Q : V → Ranking (Fin 3)}
    (hj : j ≠ i) (hjS : j ∈ S) (hq : ¬ (Q j).lt a c) :
    pivProfile a b c S i Q j = tri b c := by
  simp [pivProfile, hj, hjS, hq]

