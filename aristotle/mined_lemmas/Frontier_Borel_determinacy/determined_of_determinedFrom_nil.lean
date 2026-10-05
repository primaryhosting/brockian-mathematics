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

lemma determined_of_determinedFrom_nil {W : Set (ℕ → A)} (h : DeterminedFrom W []) :
    Determined W := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · exact Or.inl ⟨σ, fun x hplay =>
      hσ x (by simp [takePrefix]) (fun n _ hT => hplay n (Nat.zero_le n) hT)⟩
  · exact Or.inr ⟨τ, fun x hplay =>
      hτ x (by simp [takePrefix]) (fun n _ hT => hplay n (Nat.zero_le n) hT)⟩

/-!
### The play produced by a pair of strategies

This is only used to check that the notion of determinacy is not degenerate: the two
players cannot both have a winning strategy.
-/

/-- The position reached after `n` moves when I follows `σ` and II follows `τ`. -/
