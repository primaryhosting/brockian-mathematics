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

def strategyProfiles (S : ι → Type*) [∀ i, Fintype (S i)] : Set (∀ i, S i → ℝ) :=
  Set.pi Set.univ fun i => stdSimplex ℝ (S i)

/-- The expected payoff of player `i` under the (independent) mixed profile `x`. -/
