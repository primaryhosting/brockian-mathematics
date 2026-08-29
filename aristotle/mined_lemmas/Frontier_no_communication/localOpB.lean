import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix

variable {A B I : Type*} [Fintype B] [Fintype I] [DecidableEq B]

/-- The reduced state (partial trace over the second subsystem `B`) of a bipartite
state `ρ` on `A ⊗ B`.  This is the object that encodes *all* statistics available to
an observer who only has access to subsystem `A`. -/

noncomputable def localOpB (K : I → Matrix B B ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  Matrix.of fun p q => ∑ i, ∑ c, ∑ c', K i p.2 c * ρ (p.1, c) (q.1, c') * star (K i q.2 c')

/-- Helper: the Kraus completeness relation `∑ i, Kᵢ† Kᵢ = 1` written out in coordinates. -/
