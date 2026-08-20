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

theorem expectedPayoff_false (u : Bool → (∀ i, S i) → ℝ) (z : ∀ i, S i → ℝ) :
    expectedPayoff u false z = bilin (payoffMatrix u) (z false) (z true) := by
  rw [expectedPayoff, ← Equiv.sum_comp (piBoolEquiv S).symm
    (fun p => (∏ j, z j (p j)) * u false p), bilin, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.prod_bool]
  have h1 : ((piBoolEquiv S).symm (a, b)) false = a := rfl
  have h2 : ((piBoolEquiv S).symm (a, b)) true = b := rfl
  rw [h1, h2, payoffMatrix]
  ring

omit [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
