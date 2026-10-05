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

lemma winI_of_winI_append_moverI {s : Bool} {A : Set (ℕ → X)} {q : List X} {a : X}
    (hm : moverIsI s q = true) (h : WinI s A (q ++ [a])) : WinI s A q := by
  obtain ⟨σ', hσ'⟩ := h
  refine ⟨fun h => if h = q then a else σ' h, fun τ => ?_⟩
  set σ : List X → X := fun h => if h = q then a else σ' h with hσdef
  have hfirst : nextMove s σ τ q = a := by simp [nextMove, hm, hσdef]
  have h1 : play s q σ τ = play s (q ++ [a]) σ τ := by
    have := play_shift s q σ τ
    rwa [hfirst] at this
  have h2 : play s (q ++ [a]) σ τ = play s (q ++ [a]) σ' τ := by
    refine play_congr s (q ++ [a]) (fun h hh => ?_) (fun h _ => rfl)
    have hlen : q.length < h.length := by
      have := hh.length_le
      simp at this
      omega
    have hne : h ≠ q := by
      intro hEq; rw [hEq] at hlen; omega
    simp [hσdef, hne]
  rw [h1, h2]
  exact hσ' τ

/-- If player II is to move at `q` and player I has a winning strategy after every move of
player II, then player I has a winning strategy at `q`. -/
