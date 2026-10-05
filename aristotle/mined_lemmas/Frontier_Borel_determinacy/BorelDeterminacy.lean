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

def BorelDeterminacy : Prop :=
  ∀ A : Set (ℕ → ℕ), @MeasurableSet (ℕ → ℕ) (borel (ℕ → ℕ)) A → Determined A

/-- **Borel determinacy (Martin's theorem)**, reduced to Martin's unraveling lemma.

Every Borel game on Baire space `ℕ → ℕ` is determined, given the unraveling lemma
`martin_unraveling`: every Borel payoff set is covered by a game with clopen payoff (see
`Frontier.HasClopenUnraveling` and `Frontier.Covers`).  The reduction and the base case —
determinacy of clopen, indeed of all closed and all open games, `Frontier.determined_of_isClosed`
and `Frontier.determined_of_isOpen` — are proved here in full. -/
