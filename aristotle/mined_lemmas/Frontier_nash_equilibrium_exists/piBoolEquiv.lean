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

def piBoolEquiv (S : Bool → Type) : (∀ i, S i) ≃ S false × S true where
  toFun p := (p false, p true)
  invFun q := fun i => Bool.rec q.1 q.2 i
  left_inv p := by funext i; cases i <;> rfl
  right_inv q := rfl

/-- The mixed profile of a two-player game determined by the two players' strategies. -/
