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

def WinsIIFrom (W : Set (ℕ → A)) (p : List A) (τ : List A → A) : Prop :=
  ∀ x, takePrefix x p.length = p → Consistent (fun q => ¬ TurnI q) τ x p.length → x ∉ W

/-- The subgame with payoff set `W` starting at the position `p` is determined. -/
