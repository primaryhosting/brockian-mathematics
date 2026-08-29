import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Infinite two-person games of perfect information

Fix a nonempty set `X` of moves.  A *play* is an element of `ℕ → X` (for `X = ℕ` this is
Baire space); a *position* is a finite list of moves.  Players I and II alternate moves,
producing an infinite play, and player I wins iff the play belongs to the payoff set `A`.

The parameter `s : Bool` records which player moves first: for `s = false` player I moves
at positions of even length (the usual convention), for `s = true` the roles are
interchanged.  Carrying this parameter lets a single Gale–Stewart argument serve both
players.
-/

variable {X : Type*} [Inhabited X]

/-- `moverIsI s h` is `true` exactly when player I is to move at the position `h`. -/

lemma winI_of_forall_append_moverII {s : Bool} {A : Set (ℕ → X)} {q : List X}
    (hm : moverIsI s q = false) (h : ∀ a : X, WinI s A (q ++ [a])) : WinI s A q := by
  choose σ hσ using h
  refine ⟨fun h => if q.length < h.length then σ (h.getD q.length default) h else default,
    fun τ => ?_⟩
  set SS : List X → X :=
    fun h => if q.length < h.length then σ (h.getD q.length default) h else default with hSdef
  set a : X := τ q with hadef
  have hfirst : nextMove s SS τ q = a := by simp [nextMove, hm, hadef]
  have h1 : play s q SS τ = play s (q ++ [a]) SS τ := by
    have := play_shift s q SS τ
    rwa [hfirst] at this
  have hga : (q ++ [a]).getD q.length default = a := by
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  have h2 : play s (q ++ [a]) SS τ = play s (q ++ [a]) (σ a) τ := by
    refine play_congr s (q ++ [a]) (fun h hh => ?_) (fun h _ => rfl)
    have hlen : q.length + 1 ≤ h.length := by
      have := hh.length_le
      simp at this
      omega
    have hget : h.getD q.length default = a := by
      rw [getD_of_prefix hh (by simp)]
      exact hga
    have hlt : q.length < h.length := by omega
    simp only [hSdef, if_pos hlt, hget]
  rw [h1, h2]
  exact hσ a τ

/-- **The Gale–Stewart theorem.**  Every game with an open payoff set is determined, from
every position and for either player moving first. -/
