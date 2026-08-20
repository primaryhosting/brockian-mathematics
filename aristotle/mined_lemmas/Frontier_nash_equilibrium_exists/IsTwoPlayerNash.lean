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

def IsTwoPlayerNash (M N : A → B → ℝ) (x : A → ℝ) (y : B → ℝ) : Prop :=
  x ∈ stdSimplex ℝ A ∧ y ∈ stdSimplex ℝ B ∧
    (∀ x' ∈ stdSimplex ℝ A, bilin M x' y ≤ bilin M x y) ∧
    (∀ y' ∈ stdSimplex ℝ B, bilin N x y' ≤ bilin N x y)

/-- The value guaranteed to the row player by the mixed strategy `x`. -/
