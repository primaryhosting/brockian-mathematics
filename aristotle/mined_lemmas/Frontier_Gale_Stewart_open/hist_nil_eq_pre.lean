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

theorem hist_nil_eq_pre (σ τ : List A → A) (n : Nat) :
    hist σ τ [] n = pre (playSeq σ τ) n := by
  induction n with
  | zero => simp [hist, pre]
  | succ n ih => rw [hist_succ, ih, pre_succ, playSeq, ih]

/-- `WinBy S σ s` says that, from position `s`, when player I follows the strategy `σ`,
play is forced into the set `S` of positions after finitely many moves. -/
inductive WinBy (S : List A → Prop) (σ : List A → A) : List A → Prop
  | base {s : List A} : S s → WinBy S σ s
  | move_I {s : List A} : s.length % 2 = 0 → WinBy S σ (s ++ [σ s]) → WinBy S σ s
  | move_II {s : List A} : ¬ s.length % 2 = 0 → (∀ a : A, WinBy S σ (s ++ [a])) → WinBy S σ s

/-- `WinBy S σ s` only depends on the values of `σ` at positions extending `s`. -/
