import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
## Infinite two-player games of perfect information

We work with the Gale–Stewart game on a nonempty type `A`:  players I and II alternately
choose elements of `A`, player I moving first, producing an infinite play `x : ℕ → A`.
Player I wins the play iff `x ∈ W`.
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `x`. -/

def WinsIFrom (W : Set (ℕ → A)) (p : List A) (σ : List A → A) : Prop :=
  ∀ x, takePrefix x p.length = p → Consistent TurnI σ x p.length → x ∈ W

/-- `τ` is a winning strategy for player II in the subgame starting at the position `p`. -/
