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

theorem Covers.determined {proj : (ℕ → X) → (ℕ → Y)} {B : Set (ℕ → X)} {A : Set (ℕ → Y)}
    (h : Covers proj B A) (hB : Determined B) : Determined A := by
  obtain ⟨hpre, hlift⟩ := h
  rcases hB with hI | hII
  · -- player I wins the covering game
    obtain ⟨s, hs⟩ := hI
    obtain ⟨t, ht⟩ := hlift (fun n => Even n) (Or.inl rfl) s
    refine Or.inl ⟨t, fun y _ hfol => ?_⟩
    obtain ⟨x, hx, hxy⟩ := ht y hfol
    have hxB : x ∈ B := hs x (extends_nil x) hx
    rw [← hxy]
    exact (hpre x).1 hxB
  · -- player II wins the covering game
    obtain ⟨s, hs⟩ := hII
    obtain ⟨t, ht⟩ := hlift (fun n => ¬ Even n) (Or.inr rfl) s
    refine Or.inr ⟨t, fun y _ hfol => ?_⟩
    obtain ⟨x, hx, hxy⟩ := ht y hfol
    have hxB : x ∈ Bᶜ := hs x (extends_nil x) hx
    rw [← hxy]
    exact fun hy => hxB ((hpre x).2 hy)

end Covering

/-- `A` admits a **clopen unraveling**: it is covered by a game, on some alphabet, whose
payoff set is clopen.  This is the conclusion of Martin's unraveling construction. -/
