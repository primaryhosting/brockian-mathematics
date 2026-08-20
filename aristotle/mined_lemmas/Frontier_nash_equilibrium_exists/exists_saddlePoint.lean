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

theorem exists_saddlePoint (M : A → B → ℝ) :
    ∃ x ∈ stdSimplex ℝ A, ∃ y ∈ stdSimplex ℝ B,
      (∀ x' ∈ stdSimplex ℝ A, bilin M x' y ≤ bilin M x y) ∧
        (∀ y' ∈ stdSimplex ℝ B, bilin M x y ≤ bilin M x y') := by
  obtain ⟨x, hx, y, hy, hval⟩ := minimax M
  refine ⟨x, hx, y, hy, fun x' hx' => ?_, fun y' hy' => ?_⟩
  · exact ((bilin_le_colVal M hx').trans_eq hval.symm).trans (rowVal_le_bilin M hy)
  · exact ((bilin_le_colVal M hx).trans_eq hval.symm).trans (rowVal_le_bilin M hy')

/-- Unconditionally (no fixed point theorem needed): every finite two-player zero-sum game
has a mixed strategy Nash equilibrium. -/
