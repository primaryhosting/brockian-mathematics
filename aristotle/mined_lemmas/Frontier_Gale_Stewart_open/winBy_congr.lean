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

theorem winBy_congr {S : List A → Prop} {σ : List A → A} {s : List A} (h : WinBy S σ s)
    (σ' : List A → A) (hagree : ∀ u, s <+: u → σ u = σ' u) : WinBy S σ' s := by
  revert hagree
  induction h with
  | @base s hs => exact fun _ => WinBy.base hs
  | @move_I s hlen _ ih =>
      intro hag
      refine WinBy.move_I hlen ?_
      rw [← hag s (List.prefix_refl s)]
      exact ih fun u hu => hag u ((List.prefix_append s [σ s]).trans hu)
  | @move_II s hlen _ ih =>
      intro hag
      exact WinBy.move_II hlen fun a =>
        ih a fun u hu => hag u ((List.prefix_append s [a]).trans hu)

/-- Following a winning strategy, player I really does reach `S`. -/
