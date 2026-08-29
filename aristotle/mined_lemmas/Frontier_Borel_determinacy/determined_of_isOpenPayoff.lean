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

theorem determined_of_isOpenPayoff {A : Set (ℕ → X)} (hA : IsOpenPayoff A) : Determined A :=
  gale_stewart false hA []

