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


noncomputable def twoProfile (R1 R2 : Ranking (Fin 3)) (p : V) : V → Ranking (Fin 3) :=
  fun j => if j = p then R1 else R2

