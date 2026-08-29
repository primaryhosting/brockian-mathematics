/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
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

/-!
## Finite games in mixed strategies

A finite game consists of a finite set of players `ι`, a finite nonempty set of pure
strategies `S i` for each player `i`, and a payoff function
`u : ι → (∀ j, S j) → ℝ`.

A *mixed strategy* for player `i` is a probability vector on `S i`, i.e. a function
`x : S i → ℝ` with nonnegative entries summing to `1`.  A *mixed strategy profile*
assigns a mixed strategy to every player, and the expected payoff of player `i` is
the multilinear expression `∑ p, (∏ j, σ j (p j)) * u i p`.
-/

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The mixed strategy concentrated on the pure strategy `s`. -/

lemma isMixed_pureStrat {i : ι} (s : S i) : IsMixed (pureStrat s) := by
  constructor
  · intro t
    by_cases h : t = s <;> simp [pureStrat, h]
  · simp [pureStrat]

