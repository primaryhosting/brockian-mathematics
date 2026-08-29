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

lemma seqClosed_of_isClosed {W : Set (ℕ → A)} (hW : IsClosed W) : SeqClosed W := by
  intro x hall
  by_contra hxW
  obtain ⟨n, hn⟩ := seqOpen_of_isOpen hW.isOpen_compl x hxW
  obtain ⟨y, hyW, hy⟩ := hall n
  exact hn y hy hyW

/-- **Gale–Stewart theorem**: every open game is determined. -/
