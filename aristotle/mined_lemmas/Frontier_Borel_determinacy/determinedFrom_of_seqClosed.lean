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

theorem determinedFrom_of_seqClosed {W : Set (ℕ → A)} (hW : SeqClosed W) (p : List A) :
    DeterminedFrom W p := by
  classical
  -- `Dead q` : no play extending the position `q` is winning for player I
  set Dead : List A → Prop := fun q => ∀ y, takePrefix y q.length = q → y ∉ W
  by_cases hF : Force (fun q => ¬ TurnI q) Dead p
  · obtain ⟨τ, hτ⟩ := force_strategy hF
    refine Or.inr ⟨τ, fun x hx hplay hxW => ?_⟩
    obtain ⟨n, hn⟩ := hτ x hx hplay
    exact hn x (by rw [length_takePrefix]) hxW
  · obtain ⟨σ, hσ⟩ := avoid_strategy hF
    refine Or.inl ⟨σ, fun x hx hplay => ?_⟩
    have hcons : Consistent (fun q => ¬ ¬ TurnI q) σ x p.length :=
      fun n hn hT => hplay n hn (not_not.mp hT)
    have havoid := hσ x hx hcons
    refine hW x (fun n => ?_)
    by_contra hcon
    push_neg at hcon
    refine havoid (max n p.length) (le_max_right _ _) ?_
    show ∀ y, takePrefix y (takePrefix x (max n p.length)).length
      = takePrefix x (max n p.length) → y ∉ W
    intro y hy hyW
    rw [length_takePrefix] at hy
    exact hcon y hyW (takePrefix_le (le_max_left n p.length) hy)

/-- Gale–Stewart, open case: every subgame of an open game is determined
(combinatorial form). -/
