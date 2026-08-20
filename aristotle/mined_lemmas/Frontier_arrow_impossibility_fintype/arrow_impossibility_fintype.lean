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

theorem arrow_impossibility_fintype {V : Type*} [Fintype V]
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F)
    (hND : ∀ v : V, ¬ Dictator F v) : False :=
  arrow_impossibility (Finset.univ.toList) (fun v => by simp) F hU hIIA hND

/-- Positive form: on a finite set of voters, every unanimous social welfare function
satisfying independence of irrelevant alternatives has a dictator. -/
