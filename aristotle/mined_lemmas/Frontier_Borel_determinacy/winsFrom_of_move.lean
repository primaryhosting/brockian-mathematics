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

lemma winsFrom_of_move {turn : ℕ → Prop} {A : Set (ℕ → X)} {p : List X} {a : X}
    (hturn : turn p.length) (hw : WinsFrom turn A (p ++ [a])) : WinsFrom turn A p := by
  obtain ⟨σ, hσ⟩ := hw
  refine ⟨fun q => if q.length = p.length then a else σ q, ?_⟩
  intro x hx hfol
  have hxa : x p.length = a := by
    have := hfol p.length le_rfl hturn
    simpa [hx] using this
  have hext : Extends (p ++ [a]) x := by
    have : (p ++ [a]).length = p.length + 1 := by simp
    unfold Extends
    rw [this, pre_succ, hxa]
    unfold Extends at hx
    rw [hx]
  refine hσ x hext ?_
  intro n hn hturn'
  have hlen : p.length < n := by
    simpa using hn
  have hne : ¬ ((pre x n).length = p.length) := by simp; omega
  have h1 := hfol n (by omega) hturn'
  rw [h1]
  show (if (pre x n).length = p.length then a else σ (pre x n)) = σ (pre x n)
  rw [if_neg hne]

/-- If every move at `p` leads to a won position, then `p` is won.  (This is used when the
opponent moves at `p`; it happens to hold without that assumption.) -/
