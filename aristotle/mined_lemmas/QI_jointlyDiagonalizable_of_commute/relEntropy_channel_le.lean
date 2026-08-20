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


lemma relEntropy_channel_le (lam mu : I → ℝ) (A : Y → I → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ i, 0 ≤ mu i) (habs : ∀ i, mu i = 0 → lam i = 0)
    (hA : ∀ y i, 0 ≤ A y i) (hAcol : ∀ i, ∑ y, A y i = 1) :
    relEntropy (fun y => ∑ i, A y i * lam i) (fun y => ∑ i, A y i * mu i) ≤ relEntropy lam mu := by
  have step : ∀ y ∈ (Finset.univ : Finset Y),
      ((∑ i, A y i * lam i) * Real.log (∑ i, A y i * lam i)
        - (∑ i, A y i * lam i) * Real.log (∑ i, A y i * mu i))
      ≤ ∑ i, A y i * (lam i * Real.log (lam i) - lam i * Real.log (mu i)) := by
    intro y _
    have h := log_sum_ineq (fun i => A y i * lam i) (fun i => A y i * mu i)
      (fun i => mul_nonneg (hA y i) (hlam i)) (fun i => mul_nonneg (hA y i) (hmu i))
      (by
        intro i hi
        rcases mul_eq_zero.1 hi with h | h
        · simp [h]
        · simp [habs i h])
    refine h.trans_eq ?_
    rw [relEntropy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_lt_of_le (hA y i) with hAi | hAi
    · simp [← hAi]
    · rcases eq_or_lt_of_le (hlam i) with hl | hl
      · simp [← hl]
      · have hmi : 0 < mu i := by
          rcases eq_or_lt_of_le (hmu i) with h' | h'
          · exact absurd (habs i h'.symm) (ne_of_gt hl)
          · exact h'
        rw [Real.log_mul (ne_of_gt hAi) (ne_of_gt hl), Real.log_mul (ne_of_gt hAi) (ne_of_gt hmi)]
        ring
  have hsum := Finset.sum_le_sum step
  refine hsum.trans_eq ?_
  rw [Finset.sum_comm]
  rw [relEntropy]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, hAcol i, one_mul]

