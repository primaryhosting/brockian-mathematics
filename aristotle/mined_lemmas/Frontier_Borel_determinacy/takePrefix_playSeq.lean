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

lemma takePrefix_playSeq (σ τ : List A → A) (n : ℕ) :
    takePrefix (playSeq σ τ) n = playPos σ τ n := by
  induction n with
  | zero => simp [takePrefix, playPos]
  | succ n IH => rw [takePrefix_succ, IH]; rfl

