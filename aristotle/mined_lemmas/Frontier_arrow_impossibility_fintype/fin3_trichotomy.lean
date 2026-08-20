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

theorem fin3_trichotomy :
    ∀ x y c z : Fin 3, x ≠ y → c ≠ x → c ≠ y → z = x ∨ z = y ∨ z = c := by decide

/-! ## Social welfare functions and Arrow's conditions -/

universe u

variable {V : Type u}

/-- A social welfare function aggregates a profile of individual rankings into a social
ranking.  It is *unanimous* (Pareto efficient) if society prefers `a` to `b` whenever every
voter does. -/
