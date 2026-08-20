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


def tri (a b : Fin 3) : Ranking (Fin 3) :=
  if h : Inj3 (triR a b) then Ranking.ofRank (triR a b) h
  else Ranking.ofRank (fun x : Fin 3 => x.val) (fun _ _ h => Fin.eq_of_val_eq h)

