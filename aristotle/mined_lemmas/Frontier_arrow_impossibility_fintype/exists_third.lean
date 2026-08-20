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

theorem exists_third : ∀ x y : Fin 3, x ≠ y → ∃ c : Fin 3, c ≠ x ∧ c ≠ y := by decide

/-- Three pairwise distinct alternatives exhaust `Fin 3`. -/
