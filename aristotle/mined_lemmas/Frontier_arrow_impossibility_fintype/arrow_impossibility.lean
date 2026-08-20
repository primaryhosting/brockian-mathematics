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

theorem arrow_impossibility {V : Type u} (L : List V) (hL : ∀ v : V, v ∈ L)
    (F : (V → Ranking) → Ranking) (hU : Unanimous F) (hIIA : IIA F)
    (hND : ∀ v : V, ¬ Dictator F v) : False := by
  have hdec : ∀ z w : Fin 3, z ≠ w → Decisive F L z w := by
    intro z w _ p hp
    exact hU p z w fun v => hp v (hL v)
  obtain ⟨v, _, hv⟩ := exists_singleton_decisive hU hIIA L.length L (Nat.le_refl _) hdec
  refine hND v ?_
  intro p a b hab
  by_cases hab' : a = b
  · subst hab'
    exact absurd hab (prefers_irrefl _ _)
  · exact hv a b hab' p (by
      intro u hu
      rcases List.mem_singleton.mp hu with rfl
      exact hab)

/-- Equivalent positive form: any unanimous social welfare function satisfying independence
of irrelevant alternatives has a dictator. -/
