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

theorem IWins_of_all_moves {W : (Nat → A) → Prop} {p : List A} (hp : p.length % 2 = 1)
    (h : ∀ a : A, IWins W (p ++ [a])) : IWins W p := by
  have hF : ∀ a : A, ∀ τ : Strategy A, W (play (p ++ [a]) (Classical.choose (h a)) τ) :=
    fun a => Classical.choose_spec (h a)
  let σ : Strategy A := fun q => if p.length < q.length then
    Classical.choose (h (q.getD p.length default)) q else default
  have hσdef : ∀ q, σ q = if p.length < q.length then
      Classical.choose (h (q.getD p.length default)) q else default := fun _ => rfl
  refine ⟨σ, fun τ => ?_⟩
  have hstep : pos p σ τ 1 = p ++ [τ p] := by
    rw [pos_succ]; simp [hp]
  have key : ∀ k, pos p σ τ (1 + k) = pos (p ++ [τ p]) (Classical.choose (h (τ p))) τ k := by
    intro k
    rw [pos_add, hstep]
    refine pos_congr ?_ (fun _ _ => rfl) k
    intro q hq
    have hlen : p.length < q.length := by
      have := hq.length_le; simp at this; omega
    have hget : q.getD p.length default = τ p := by
      rw [getD_of_prefix hq (by simp)]
      simp [List.getD_eq_getElem?_getD]
    rw [hσdef, if_pos hlen, hget]
  rw [play_eq_of_shift key (by simp)]
  exact hF (τ p) τ

/-- **Gale–Stewart theorem.**  Every open game is determined: if the payoff set `W` is open in
the product topology on `Nat → A` (`A` discrete), then either Player I has a strategy `σ` winning
against every strategy of Player II, or Player II has a strategy `τ` winning against every
strategy of Player I. -/
