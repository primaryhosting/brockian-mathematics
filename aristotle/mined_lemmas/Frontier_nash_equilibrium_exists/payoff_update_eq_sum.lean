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

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/

lemma payoff_update_eq_sum (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ)
    (z : S i → ℝ) :
    payoff u i (Function.update x i z) = ∑ s, z s * devPayoff u i s x := by
  rw [payoff_update]
  simp only [devPayoff, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (p i)]
  · simp
  · intro s _ hs
    simp [Ne.symm hs]
  · intro h
    exact absurd (mem_univ (p i)) h

