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


lemma mutualInfo_eq_sum_relEntropy (p : X → ℝ) (Q : X → Y → ℝ) :
    ∑ x, p x * relEntropy (Q x) (fun y => ∑ x', p x' * Q x' y)
      = shannonEntropy (fun y => ∑ x, p x * Q x y) - ∑ x, p x * shannonEntropy (Q x) := by
  set Qbar : Y → ℝ := fun y => ∑ x, p x * Q x y with hQbar
  have e1 : ∀ x, relEntropy (Q x) Qbar
      = (-shannonEntropy (Q x)) - ∑ y, Q x y * Real.log (Qbar y) := by
    intro x
    rw [relEntropy, Finset.sum_sub_distrib, shannonEntropy_eq_neg_sum, neg_neg]
  have e2 : ∑ x, p x * (∑ y, Q x y * Real.log (Qbar y)) = -shannonEntropy Qbar := by
    rw [shannonEntropy_eq_neg_sum, neg_neg]
    have : ∀ x, p x * (∑ y, Q x y * Real.log (Qbar y))
        = ∑ y, p x * Q x y * Real.log (Qbar y) := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul]
  calc ∑ x, p x * relEntropy (Q x) Qbar
      = ∑ x, (p x * (-shannonEntropy (Q x)) - p x * ∑ y, Q x y * Real.log (Qbar y)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [e1 x, mul_sub]
    _ = (∑ x, p x * (-shannonEntropy (Q x)))
          - ∑ x, p x * ∑ y, Q x y * Real.log (Qbar y) := Finset.sum_sub_distrib _ _
    _ = shannonEntropy Qbar - ∑ x, p x * shannonEntropy (Q x) := by
        rw [e2]
        simp [Finset.sum_neg_distrib]
        ring

/-- **Classical Holevo / data-processing bound**: processing the letter alphabet `I` through a
stochastic channel `A` cannot increase the mutual information with `X`. -/
