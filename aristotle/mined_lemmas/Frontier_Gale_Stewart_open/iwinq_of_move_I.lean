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

theorem iwinq_of_move_I {S : List A → Prop} {s : List A} (hs : s.length % 2 = 0) {a : A}
    (h : IWinQ S (s ++ [a])) : IWinQ S s := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun u => if u.length = s.length then a else σ u, ?_⟩
  have hw : WinBy S (fun u => if u.length = s.length then a else σ u) (s ++ [a]) := by
    refine winBy_congr hσ _ ?_
    intro u hu
    have hlen : s.length + 1 ≤ u.length := by
      have := hu.length_le
      simpa using this
    have : ¬ u.length = s.length := by omega
    simp [this]
  refine WinBy.move_I hs ?_
  simpa using hw

