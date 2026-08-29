/-
/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
Every open game is determined (Gale–Stewart).

We consider the infinite two-player game on a nonempty set `A` of moves: the two players
alternately choose elements of `A`, player I moving at the even stages and player II at the odd
stages, producing a play `x : ℕ → A`.  Player I wins the play `x` iff `x ∈ W`, where `W` is the
payoff set.  A *strategy* is a function `List A → A` assigning a move to every position (finite
sequence of previous moves).

The theorem states: if `W` is open in the product topology on `ℕ → A` (with `A` discrete), then
either player I has a winning strategy or player II has one.
-/

namespace Frontier

open scoped Classical

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

theorem winI_of_forall_snoc [Inhabited A] {W : Set (ℕ → A)} {r : List A}
    (h : ∀ b, WinI W (r ++ [b])) : WinI W r := by
  choose S hS using h
  refine ⟨fun r' => if hlt : r.length < r'.length then S (r'[r.length]'hlt) r' else default,
    fun x hx hfol => ?_⟩
  set b := x r.length with hb
  have hpref : pref x (r ++ [b]).length = r ++ [b] := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [pref_succ, hx]
  refine hS b x hpref (fun n hn hne => ?_)
  have hlen : r.length + 1 ≤ n := by simpa using hn
  have hlt : r.length < (pref x n).length := by rw [length_pref]; omega
  have := hfol n (by omega) hne
  rw [this]
  simp only [dif_pos hlt, getElem_pref x (show r.length < n by omega)]
  rw [hb]

