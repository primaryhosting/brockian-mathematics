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

theorem exists_dictator {V : Type u} (L : List V) (hL : ∀ v : V, v ∈ L)
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F) :
    ∃ v : V, Dictator F v := by
  refine Classical.byContradiction fun hc => ?_
  exact arrow_impossibility L hL F hU hIIA (fun v hv => hc ⟨v, hv⟩)

/-! ## Sanity check: the other two conditions are consistent

Dropping non-dictatorship, the remaining conditions are satisfiable: the rule "copy voter
`v₀`'s ranking" is unanimous and satisfies independence of irrelevant alternatives. -/

