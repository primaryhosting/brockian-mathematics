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

theorem pos_congr {p : List A} {σ σ' τ τ' : Strategy A}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) (k : Nat) :
    pos p σ τ k = pos p σ' τ' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pos_succ, pos_succ, ih, hσ _ (by rw [← ih]; exact prefix_pos p σ τ k),
      hτ _ (by rw [← ih]; exact prefix_pos p σ τ k)]

omit [Inhabited A] in
/-- Playing from `p` for `j + k` moves is the same as playing from `pos p σ τ j` for `k` moves. -/
