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

lemma le_payoff_of_pure {u : ι → (∀ j, S j) → ℝ} {i : ι} {σ : ∀ j, S j → ℝ}
    (h : ∀ s, payoff u i (Function.update σ i (pureStrat s)) ≤ payoff u i σ)
    (τ : S i → ℝ) (hτ : IsMixed τ) :
    payoff u i (Function.update σ i τ) ≤ payoff u i σ := by
  rw [payoff_update_eq_sum]
  calc ∑ s, τ s * payoff u i (Function.update σ i (pureStrat s))
      ≤ ∑ _s : S i, τ _s * payoff u i σ := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (h s) (hτ.1 s)
    _ = payoff u i σ := by rw [← Finset.sum_mul, hτ.2, one_mul]

/-- Some pure strategy in the support of `σ i` is not better than `σ i` itself. -/
