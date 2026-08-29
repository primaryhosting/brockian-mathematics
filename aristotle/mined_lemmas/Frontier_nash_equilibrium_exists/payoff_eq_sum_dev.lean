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

lemma payoff_eq_sum_dev (u : I → ((i : I) → S i) → ℝ) (i : I) (σ : (i : I) → S i → ℝ) :
    payoff u i σ = ∑ a : S i, σ i a * dev u i a σ := by
  simp only [payoff, dev, prod_update_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_prod_erase univ (fun j => σ j (s j)) (mem_univ i)]
  have key : ∀ x : S i,
      σ i x * ((pureMix x (s i) * ∏ j ∈ univ.erase i, σ j (s j)) * u i s)
        = if s i = x then σ i (s i) * ((∏ j ∈ univ.erase i, σ j (s j)) * u i s) else 0 := by
    intro x; by_cases h : s i = x <;> simp [pureMix, h]
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_ite_eq]
  simp
  ring

