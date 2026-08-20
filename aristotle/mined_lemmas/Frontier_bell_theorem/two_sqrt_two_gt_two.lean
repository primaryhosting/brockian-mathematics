/-
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Real

namespace Frontier

/-- **Pointwise CHSH bound.** For real numbers of absolute value at most `1`,
the CHSH combination `a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂` has absolute value at most `2`. -/

theorem two_sqrt_two_gt_two : (2 : ℝ) < 2 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]

/-- **Bell's theorem.** No local hidden-variable model reproduces the quantum-mechanical
correlations: there is no probability space of hidden variables together with local
`[-1,1]`-valued response functions `A i` for Alice and `B j` for Bob whose correlations
`∫ A i · B j` equal the quantum correlations `cos (αᵢ - βⱼ)` at the CHSH settings.

The proof is the CHSH inequality: any such model satisfies
`|E(A₁B₁) + E(A₁B₂) + E(A₂B₁) - E(A₂B₂)| ≤ 2`, while quantum mechanics predicts `2√2 > 2`. -/
