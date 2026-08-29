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

theorem pos_prefix_mono (p : List A) (σ τ : Strategy A) {k l : Nat} (h : k ≤ l) :
    pos p σ τ k <+: pos p σ τ l := by
  induction l with
  | zero =>
    have : k = 0 := Nat.le_zero.mp h
    subst this; exact List.prefix_rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h' | h'
    · exact (ih (by omega)).trans (pos_prefix_succ p σ τ l)
    · have : k = l + 1 := by omega
      subst this; exact List.prefix_rfl

omit [Inhabited A] in
