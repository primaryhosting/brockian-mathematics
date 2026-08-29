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

lemma isNashEquilibrium_of_pure (u : ι → (∀ j, S j) → ℝ) {x : ∀ j, S j → ℝ}
    (hx : IsMixed x) (h : ∀ (i : ι) (s : S i), devPayoff u i s x ≤ payoff u i x) :
    IsNashEquilibrium u x := by
  refine ⟨hx, fun i z hz => ?_⟩
  rw [payoff_update_eq_sum]
  calc ∑ s, z s * devPayoff u i s x ≤ ∑ _s : S i, z _s * payoff u i x := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (h i s) (hz.1 s)
    _ = payoff u i x := by rw [← Finset.sum_mul, hz.2, one_mul]

/-! ## The strategy space is nonempty, compact and convex -/

omit [Fintype ι] [DecidableEq ι] in
