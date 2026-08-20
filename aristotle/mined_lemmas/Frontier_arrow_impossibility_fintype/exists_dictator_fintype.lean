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

theorem exists_dictator_fintype {V : Type*} [Fintype V]
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F) :
    ∃ v : V, Dictator F v :=
  exists_dictator (Finset.univ.toList) (fun v => by simp) F hU hIIA

end Frontier

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

attribute [local instance] Classical.propDecidable

/-! ## Rankings of three alternatives

The three alternatives are the elements of `Fin 3`.  A *ranking* is a strict linear order on
them, encoded by its rank function: `r.rank a` is the position of alternative `a` (smaller is
better), and distinct alternatives get distinct positions. -/

/-- A strict ranking of the three alternatives, encoded by an injective rank function. -/
structure Ranking where
  /-- The position of an alternative; smaller means more preferred. -/
  rank : Fin 3 → Nat
  /-- Distinct alternatives occupy distinct positions (no ties). -/
  inj : ∀ a b, rank a = rank b → a = b

/-- `prefers r a b` says that the ranking `r` strictly prefers `a` to `b`. -/
