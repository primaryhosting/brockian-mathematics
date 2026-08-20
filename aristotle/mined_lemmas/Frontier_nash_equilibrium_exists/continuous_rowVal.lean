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

theorem continuous_rowVal (M : A → B → ℝ) : Continuous (rowVal M) :=
  Continuous.finset_inf'_apply univ_nonempty fun _ _ =>
    continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const

omit [Nonempty B] [DecidableEq A] [DecidableEq B] in
