import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]


lemma shannonEntropy_eq_neg_sum (P : Y → ℝ) :
    shannonEntropy P = -∑ y, P y * Real.log (P y) := by
  rw [shannonEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => by simp [Real.negMulLog]

/-- Mutual information (as `H(P̄) - ∑ₓ pₓ H(Pₓ)`) equals the average divergence from the
mean distribution. -/
