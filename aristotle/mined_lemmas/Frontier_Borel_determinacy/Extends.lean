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

lemma Extends.eq_of_lt {p : List X} {x : ℕ → X} (h : Extends p x) {i : ℕ}
    (hi : i < p.length) : p[i] = x i := by
  have h2 : (pre x p.length)[i]'(by simpa using hi) = p[i] :=
    List.getElem_of_eq h (by simpa using hi)
  rw [← h2, pre_getElem]

/-- From the position `p` on, the play `x` follows the strategy `σ` of the player whose
moves are those at the times in `turn`. -/
