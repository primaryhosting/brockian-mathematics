/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/

theorem semiDecisive_of_decisive {F : (V → Ranking) → Ranking} {S : List V} {a b : Fin 3}
    (h : Decisive F S a b) : SemiDecisive F S a b := fun p hp _ => h p hp

/-- Field expansion, first half: a coalition semi-decisive for `(a,b)` is decisive for `(a,c)`. -/
