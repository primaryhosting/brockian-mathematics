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

lemma winsFrom_of_forall_moves [Inhabited X] {turn : ℕ → Prop} {A : Set (ℕ → X)} {p : List X}
    (hw : ∀ a : X, WinsFrom turn A (p ++ [a])) :
    WinsFrom turn A p := by
  choose f hf using hw
  refine ⟨fun q => if h : p.length < q.length then f q[p.length] q else default, ?_⟩
  intro x hx hfol
  set a := x p.length with ha
  have hext : Extends (p ++ [a]) x := by
    have hlen : (p ++ [a]).length = p.length + 1 := by simp
    unfold Extends
    rw [hlen, pre_succ, ha]
    unfold Extends at hx
    rw [hx]
  refine hf a x hext ?_
  intro n hn hturn'
  have hlen : p.length < n := by simpa using hn
  have h1 := hfol n (by omega) hturn'
  rw [h1]
  have hq : p.length < (pre x n).length := by simpa using hlen
  show (if h : p.length < (pre x n).length then f (pre x n)[p.length] (pre x n) else default)
      = f a (pre x n)
  rw [dif_pos hq, pre_getElem]

/-! ## The Gale–Stewart theorem: closed games are determined

This is the base case of Borel determinacy.  We prove it in a general form: for any turn
predicate and any closed payoff set `A`, either the player with turn set `turn` has a
winning strategy for `A`, or the other player has a winning strategy for `Aᶜ`.
-/

/-- Closedness of a payoff set, phrased combinatorially: any play *not* in `A` has a finite
initial segment all of whose extensions avoid `A`.  For the product topology this is
equivalent to topological closedness, see `cylClosed_of_isClosed`. -/
