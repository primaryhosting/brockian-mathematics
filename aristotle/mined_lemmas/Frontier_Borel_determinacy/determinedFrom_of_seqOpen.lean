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

theorem determinedFrom_of_seqOpen {W : Set (ℕ → A)} (hW : SeqOpen W) (p : List A) :
    DeterminedFrom W p := by
  classical
  -- `Secured q` : every play extending the position `q` is winning for player I
  set Secured : List A → Prop := fun q => ∀ y, takePrefix y q.length = q → y ∈ W
  by_cases hF : Force TurnI Secured p
  · obtain ⟨σ, hσ⟩ := force_strategy hF
    refine Or.inl ⟨σ, fun x hx hplay => ?_⟩
    obtain ⟨n, hn⟩ := hσ x hx hplay
    exact hn x (by rw [length_takePrefix])
  · obtain ⟨τ, hτ⟩ := avoid_strategy hF
    refine Or.inr ⟨τ, fun x hx hplay hxW => ?_⟩
    have havoid := hτ x hx hplay
    obtain ⟨n, hn⟩ := hW x hxW
    refine havoid (max n p.length) (le_max_right _ _) ?_
    show ∀ y, takePrefix y (takePrefix x (max n p.length)).length
      = takePrefix x (max n p.length) → y ∈ W
    intro y hy
    rw [length_takePrefix] at hy
    exact hn y (takePrefix_le (le_max_left n p.length) hy)

/-- Gale–Stewart, closed case (combinatorial form). -/
