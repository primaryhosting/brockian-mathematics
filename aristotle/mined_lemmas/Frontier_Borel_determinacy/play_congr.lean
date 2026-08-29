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

lemma play_congr (s : Bool) (p : List X) {σ τ σ' τ' : List X → X}
    (hσ : ∀ h : List X, p <+: h → σ h = σ' h) (hτ : ∀ h : List X, p <+: h → τ h = τ' h) :
    play s p σ τ = play s p σ' τ' := by
  funext k
  simp only [play, hist_congr s p hσ hτ]

/-! ### Sanity checks: the game conventions are the intended ones

Player I controls the even coordinates of the play and player II the odd ones. -/

example : WinI false {x : ℕ → ℕ | x 0 = 1} [] :=
  ⟨fun _ => 1, fun _ => rfl⟩

example : WinII false {x : ℕ → ℕ | x 1 = 1} [] :=
  ⟨fun _ => 0, fun _ => by simp [play, hist, nextMove, moverIsI]⟩

/-! ## Open payoff sets -/

/-- A payoff set is *open* in the combinatorial sense if membership of any of its elements
is already guaranteed by a finite initial segment of that element. -/
