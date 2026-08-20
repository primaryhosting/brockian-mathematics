/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

theorem no_winT_strategy {W : Set (List X)} (h : IsEmpty (WinT W ([] : List X))) :
    ∃ τ : List X → X, ∀ a : ℕ → X, FollowsII τ a → ∀ m, hist a m ∉ W := by
  classical
  have hnotW : ∀ q : List X, IsEmpty (WinT W q) → q ∉ W := fun q hq hqW => hq.false (WinT.base hqW)
  have heven : ∀ q : List X, Even q.length → IsEmpty (WinT W q) →
      ∀ x, IsEmpty (WinT W (q ++ [x])) := by
    intro q hq hnd x
    exact ⟨fun t => hnd.false (WinT.moveI x hq t)⟩
  have hodd : ∀ q : List X, Odd q.length → IsEmpty (WinT W q) →
      ∃ x, IsEmpty (WinT W (q ++ [x])) := by
    intro q hq hnd
    by_contra hcon
    push_neg at hcon
    have hne : ∀ x, Nonempty (WinT W (q ++ [x])) := hcon
    exact hnd.false (WinT.moveII hq (fun x => Classical.choice (hne x)))
  refine ⟨fun q => if hq : ∃ x, IsEmpty (WinT W (q ++ [x])) then hq.choose
    else Classical.arbitrary X, fun a ha m => ?_⟩
  have key : ∀ m, IsEmpty (WinT W (hist a m)) := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
        rcases Nat.even_or_odd m with hm | hm
        · have := heven (hist a m) (by simpa using hm) ih (a m)
          simpa using this
        · have hex : ∃ x, IsEmpty (WinT W (hist a m ++ [x])) :=
            hodd (hist a m) (by simpa using hm) ih
          have ham : a m = hex.choose := by
            rw [ha m hm]
            simp [hex]
          rw [hist_succ, ham]
          exact hex.choose_spec
  exact hnotW _ (key m)

end GaleStewart

namespace Frontier

open GaleStewart

/-- **Gale–Stewart**: every open game is determined.  The moves are elements of a nonempty
discrete space `X`; a play is a sequence `a : ℕ → X`, player I choosing `a 0, a 2, …` and
player II choosing `a 1, a 3, …`.  Player I wins the play iff `a ∈ A`.  If the payoff set `A`
is open in the product topology, then one of the players has a winning strategy.

(The discreteness hypothesis is part of the usual statement; the proof below in fact only uses
that `A` is open in the product topology of whatever topology `X` carries.) -/
