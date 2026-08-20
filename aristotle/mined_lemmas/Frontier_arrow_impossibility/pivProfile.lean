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


noncomputable def pivProfile (a b c : Fin 3) (S : List V) (i : V)
    (Q : V → Ranking (Fin 3)) : V → Ranking (Fin 3) :=
  fun j =>
    if j = i then tri a b
    else if j ∈ S then (if (Q j).lt a c then tri b a else tri b c)
    else (if (Q j).lt a c then tri a c else tri c a)

