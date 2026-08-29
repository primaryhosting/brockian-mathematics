import Mathlib
import RequestProject.GaleStewartOpen

/-!
# Gale–Stewart for topologically open payoff sets

`Frontier.Gale_Stewart_open` states openness of the payoff set combinatorially (membership of a
play is guaranteed by a finite initial segment of it).  Here we record the corollary phrased with
Mathlib's product topology on `ℕ → A`.
-/

namespace Frontier

universe u

variable {A : Type u}

/-- **Gale–Stewart theorem**, topological form: if the payoff set `W` is open in the product
topology on `ℕ → A` (for instance, the product of discrete topologies), then the associated
infinite game is determined. -/

theorem iwinq_of_move_II [Nonempty A] {S : List A → Prop} {s : List A} (hs : ¬ s.length % 2 = 0)
    (h : ∀ a : A, IWinQ S (s ++ [a])) : IWinQ S s := by
  have hF : ∀ a, WinBy S (Classical.choose (h a)) (s ++ [a]) := fun a => Classical.choose_spec (h a)
  refine ⟨fun u => if hlt : s.length < u.length then Classical.choose (h (u[s.length]'hlt)) u
    else Classical.choice inferInstance, ?_⟩
  refine WinBy.move_II hs fun a => ?_
  refine winBy_congr (hF a) _ ?_
  intro u hu
  have hlen : s.length + 1 ≤ u.length := by
    have := hu.length_le
    simpa using this
  have hlt : s.length < u.length := hlen
  have hidx : u[s.length]'hlt = a := by
    have hb : s.length < (s ++ [a]).length := by simp
    have := hu.getElem hb
    rw [← this]
    rw [List.getElem_append_right (Nat.le_refl s.length)]
    simp
  rw [dif_pos hlt, hidx]

/-- **Gale–Stewart theorem for open games.**  Two players alternately choose elements of a
nonempty set `A` of moves (player I choosing `x 0, x 2, …`, player II choosing `x 1, x 3, …`),
producing an infinite play `x : Nat → A`; player I wins iff `W x`.  Strategies are functions
from the current position (the list of moves played so far) to the next move.  If the payoff
set `W` is open — i.e. membership of any of its elements is already guaranteed by a finite
initial segment of it — then the game is determined: one of the two players has a winning
strategy. -/
