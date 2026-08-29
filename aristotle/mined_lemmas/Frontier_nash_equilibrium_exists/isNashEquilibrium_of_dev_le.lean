import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Set

namespace Frontier

universe u

/-! ## Finite games in mixed strategies

A finite game is given by a finite type of players `I`, a finite nonempty type of pure
strategies `S i` for each player, and a real payoff function
`u : I → ((i : I) → S i) → ℝ`.
-/

variable {I : Type u} [Fintype I] [DecidableEq I]
  {S : I → Type u} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles: for each player, a probability distribution on
that player's pure strategies. -/

lemma isNashEquilibrium_of_dev_le (u : I → ((i : I) → S i) → ℝ) (σ : (i : I) → S i → ℝ)
    (h : ∀ i : I, ∀ a : S i, dev u i a σ ≤ payoff u i σ) : IsNashEquilibrium u σ := by
  intro i τ hτ
  obtain ⟨hτ0, hτ1⟩ := hτ
  rw [payoff_update_eq_sum_dev]
  calc ∑ a : S i, τ a * dev u i a σ ≤ ∑ a : S i, τ a * payoff u i σ := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (h i a) (hτ0 a)
    _ = payoff u i σ := by rw [← Finset.sum_mul, hτ1, one_mul]

/-! ## The Nash improvement map -/

/-- The improvement of player `i` from switching to the pure strategy `a`, truncated
below at zero. -/
