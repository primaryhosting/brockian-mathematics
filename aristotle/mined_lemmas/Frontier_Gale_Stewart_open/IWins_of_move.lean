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

theorem IWins_of_move {W : (Nat → A) → Prop} {p : List A} (hp : p.length % 2 = 0) {a : A}
    (h : IWins W (p ++ [a])) : IWins W p := by
  obtain ⟨σ', hσ'⟩ := h
  let σ : Strategy A := fun q => if q = p then a else σ' q
  have hσdef : ∀ q, σ q = if q = p then a else σ' q := fun _ => rfl
  refine ⟨σ, fun τ => ?_⟩
  have hstep : pos p σ τ 1 = p ++ [a] := by
    rw [pos_succ]; simp [hp, hσdef]
  have key : ∀ k, pos p σ τ (1 + k) = pos (p ++ [a]) σ' τ k := by
    intro k
    rw [pos_add, hstep]
    refine pos_congr ?_ (fun _ _ => rfl) k
    intro q hq
    have hne : q ≠ p := by
      intro hqp
      subst hqp
      have := hq.length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega
    rw [hσdef, if_neg hne]
  rw [play_eq_of_shift key (by simp)]
  exact hσ' τ

/-- If Player II is to move at `p` and every move leads to a position winning for Player I, then
`p` is winning for Player I. -/
