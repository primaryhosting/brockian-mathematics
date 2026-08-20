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

theorem prefers_total {r : Ranking} {a b : Fin 3} (hab : a ≠ b) (h : ¬ prefers r a b) :
    prefers r b a := by
  rcases Nat.lt_trichotomy (r.rank a) (r.rank b) with h₁ | h₁ | h₁
  · exact absurd h₁ h
  · exact absurd (r.inj a b h₁) hab
  · exact h₁

/-! ## Building rankings -/

/-- The rank function of the ranking `x ≻ y ≻ z`. -/
