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

lemma takePrefix_le {x y : ℕ → A} {n m : ℕ} (hnm : n ≤ m)
    (h : takePrefix y m = takePrefix x m) : takePrefix y n = takePrefix x n :=
  takePrefix_eq_iff.mpr fun i hi => takePrefix_eq_iff.mp h i (lt_of_lt_of_le hi hnm)

/-- The game starting at the empty position is the original game. -/
