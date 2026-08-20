import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

variable {X : Type u}

/-- A strategy assigns a move to every finite position of the game. -/
abbrev Strategy (X : Type u) := List X → X

/-- The move played at position `q`: player I (resp. II) moves at positions of
even (resp. odd) length. -/

theorem not_IWins_and_IIWins (A : Set (ℕ → X)) (p : List X) :
    ¬ (IWins A p ∧ IIWins A p) := by
  rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
  exact hτ σ (hσ τ)

/-! ### Topological form of the Gale–Stewart theorem -/

section Topology

variable [TopologicalSpace X]

omit [Nonempty X] in
/-- An open subset of the product space `ℕ → X` is an open payoff set. -/
