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


noncomputable def swapProfile (a b c : Fin 3) (P : V → Ranking (Fin 3)) :
    V → Ranking (Fin 3) :=
  fun j => if (P j).lt b a then tri b c else tri c a

