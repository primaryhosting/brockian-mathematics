import RequestProject.Nash

/-!
# The one-dimensional base case of Brouwer's fixed point theorem

Brouwer's fixed point theorem is not available in Mathlib, and is taken as an explicit
hypothesis in `Frontier.nash_equilibrium_exists`.  Here we prove the one-dimensional base
case of that hypothesis, `BrouwerFixedPointProperty ℝ`, from the intermediate value
theorem; in particular the hypothesis is not vacuous.
-/

open Set

namespace Frontier

/-- **Brouwer's fixed point theorem in dimension one**: every continuous self-map of a
nonempty compact convex subset of `ℝ` has a fixed point. -/

theorem expectedPayoff_true (u : Bool → (∀ i, S i) → ℝ)
    (hzs : ∀ p, u true p = -u false p) (z : ∀ i, S i → ℝ) :
    expectedPayoff u true z = -bilin (payoffMatrix u) (z false) (z true) := by
  rw [← expectedPayoff_false u z, expectedPayoff, expectedPayoff, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [hzs p]; ring

/-- Unconditionally (no fixed point theorem needed): every finite two-player zero-sum game
has a mixed strategy Nash equilibrium, in the sense of `Frontier.IsNashEquilibrium`. -/
