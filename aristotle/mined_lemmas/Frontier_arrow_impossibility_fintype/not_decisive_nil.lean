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

theorem not_decisive_nil {F : (V → Ranking) → Ranking}
    (h : ∀ z w : Fin 3, z ≠ w → Decisive F ([] : List V) z w) : False := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun _ => mkRank 0 1 2 h01 h02 h12 := ⟨_, rfl⟩
  have h1 : prefers (F p) 0 1 := h 0 1 h01 p (by intro v hv; cases hv)
  have h2 : prefers (F p) 1 0 := h 1 0 (Ne.symm h01) p (by intro v hv; cases hv)
  exact prefers_asymm h1 h2

/-- Contraction of decisive coalitions: a coalition that is decisive for every pair contains
a single voter that is decisive for every pair. -/
