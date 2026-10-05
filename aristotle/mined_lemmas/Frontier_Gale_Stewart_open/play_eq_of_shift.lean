import Mathlib
import RequestProject.Frontier

/-!
# Gale–Stewart for open games: the topological form

`RequestProject.Frontier` proves the Gale–Stewart theorem `Frontier.Gale_Stewart_open` with the
combinatorial formulation of openness (`Frontier.IsOpenPayoff`).  Here we check that this
hypothesis is exactly openness of the payoff set in the product topology on `ℕ → A` where `A`
carries the discrete topology, and record the resulting topological statement
`Frontier.Gale_Stewart_open_topological`.

(Discreteness of `A` is only needed for the converse implication
`Frontier.isOpen_of_isOpenPayoff`; openness for an arbitrary topology on `A` already implies the
combinatorial condition, hence determinacy.)
-/

namespace Frontier

universe u

variable {A : Type u} [TopologicalSpace A]

/-- An open set of the product topology on `ℕ → A` is an open payoff set. -/

theorem play_eq_of_shift {p p' : List A} {σ σ' τ τ' : Strategy A} {j : Nat}
    (h : ∀ k, pos p σ τ (j + k) = pos p' σ' τ' k) (hlen : p'.length = p.length + j) :
    play p σ τ = play p' σ' τ' := by
  funext n
  have h1 : play p σ τ n = (pos p σ τ (j + (n + 1))).getD n default :=
    play_eq_getD p σ τ (by omega)
  have h2 : play p' σ' τ' n = (pos p' σ' τ' (n + 1)).getD n default :=
    play_eq_getD p' σ' τ' (by omega)
  rw [h1, h2, h]

/-- `W` is open in the product topology on `Nat → A` with `A` discrete: every play in `W` has a
finite initial segment all of whose extensions lie in `W`. -/
