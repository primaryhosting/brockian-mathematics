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

def Unraveling.ofClosed (A : Set (ℕ → X)) (hA : IsOpenPayoff Aᶜ) : Unraveling A where
  Y := X
  proj := id
  payoff := A
  simple_payoff := Or.inr hA
  pullback := rfl
  liftI := id
  liftII := id
  liftI_spec := fun _ τ => ⟨τ, rfl⟩
  liftII_spec := fun _ σ => ⟨σ, rfl⟩

omit [TopologicalSpace X] in
/-- **Martin's reduction**: a payoff set admitting an unraveling is determined. -/
