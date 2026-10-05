import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Infinite games: positions, strategies, winning strategies

We consider infinite two-player games with perfect information played on an alphabet `X`.
A *play* is a sequence `x : ℕ → X`; the move at time `n` is `x n`.  Which player moves at
time `n` is recorded by a predicate `turn : ℕ → Prop` (the *turn set* of the player under
consideration).  In the classical game `G(A)` on Baire space, player I moves at the even
times and player II at the odd times, and player I wins the play `x` iff `x ∈ A`.
-/

variable {X : Type*}

/-- The position reached after the first `n` moves of the play `x`. -/

theorem determined_of_cylOpen [Inhabited X] {A : Set (ℕ → X)} (hA : CylClosed Aᶜ) :
    Determined A := by
  rcases gale_stewart (fun n => ¬ Even n) Aᶜ hA with h | h
  · exact Or.inr h
  · left
    obtain ⟨σ, hσ⟩ := h
    refine ⟨σ, fun x hx hfol => ?_⟩
    have : x ∈ Aᶜᶜ := hσ x hx (fun n hn hturn => hfol n hn (by simpa using hturn))
    simpa using this

/-- Topologically closed games (on any alphabet) are determined. -/
