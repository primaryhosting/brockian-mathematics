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

noncomputable def colVal (M : A → B → ℝ) (y : B → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun a => ∑ b, y b * M a b

omit [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B] in
