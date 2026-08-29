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

theorem isOpen_of_isOpenPayoff [DiscreteTopology A] {W : Set (ℕ → A)}
    (hW : IsOpenPayoff (fun x => x ∈ W)) : IsOpen W := by
  rw [isOpen_pi_iff]
  intro x hx
  obtain ⟨n, hn⟩ := hW x hx
  refine ⟨Finset.range n, fun i => {x i}, fun i _ => ⟨isOpen_discrete _, rfl⟩, fun y hy => ?_⟩
  exact hn y fun i hi => hy i (Finset.mem_range.mpr hi)

/-- **Gale–Stewart theorem, topological form.**  If the payoff set `W` is open in the product
topology on `ℕ → A` (for `A` discrete, this is the usual topology on the space of plays), then
the game is determined. -/
