import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/

def IWinsFrom (W : Set (ℕ → A)) (p : List A) : Prop :=
  ∃ σ : Strategy A, ∀ f : ℕ → A, takeF f p.length = p →
    (∀ n, p.length ≤ n → Even n → f n = σ (takeF f n)) → f ∈ W

/-- Openness in the product topology: every play in `W` has a finite initial segment
all of whose extensions lie in `W`. -/
