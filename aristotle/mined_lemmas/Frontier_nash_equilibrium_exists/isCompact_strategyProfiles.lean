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

theorem isCompact_strategyProfiles : IsCompact (strategyProfiles S) :=
  isCompact_univ_pi fun i => isCompact_stdSimplex (S i)

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
