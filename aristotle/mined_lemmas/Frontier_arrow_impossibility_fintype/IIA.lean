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

def IIA (F : (V → Ranking) → Ranking) : Prop :=
  ∀ (p q : V → Ranking) (a b : Fin 3),
    (∀ v, prefers (p v) a b ↔ prefers (q v) a b) → (prefers (F p) a b ↔ prefers (F q) a b)

/-- Voter `v` is a *dictator* for `F` if the social preference always follows `v`'s. -/
