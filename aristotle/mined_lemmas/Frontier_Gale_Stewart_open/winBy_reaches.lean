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

theorem winBy_reaches {S : List A → Prop} {σ : List A → A} {s : List A} (h : WinBy S σ s) :
    ∀ τ : List A → A, ∃ n, S (hist σ τ s n) := by
  induction h with
  | @base s hs => exact fun _ => ⟨0, hs⟩
  | @move_I s hlen _ ih =>
      intro τ
      obtain ⟨n, hn⟩ := ih τ
      exact ⟨n + 1, by simpa [hist, nextMove, hlen] using hn⟩
  | @move_II s hlen _ ih =>
      intro τ
      obtain ⟨n, hn⟩ := ih (τ s) τ
      exact ⟨n + 1, by simpa [hist, nextMove, hlen] using hn⟩

/-- Player I has a strategy that forces the play into `S` in finitely many moves,
starting from position `s`. -/
