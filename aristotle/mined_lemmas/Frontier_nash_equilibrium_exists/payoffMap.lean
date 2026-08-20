/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

noncomputable def payoffMap (A : m → n → ℝ) : (n → ℝ) →ₗ[ℝ] (m → ℝ) where
  toFun := payoffVec A
  map_add' y₁ y₂ := by
    funext i
    simp [payoffVec, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    funext i
    simp [payoffVec, Finset.mul_sum, mul_assoc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
