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


lemma log_sum_ineq (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log (∑ i, a i) - (∑ i, a i) * Real.log (∑ i, b i) ≤ relEntropy a b := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hA0 with hA_eq | hApos
  · -- all `a i = 0`
    have hzero : ∀ i, a i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 hA_eq.symm i (Finset.mem_univ i)
      exact this
    have hA' : A = 0 := hA_eq.symm
    simp [relEntropy, hzero, hA']
  · have hBpos : 0 < B := by
      rcases eq_or_lt_of_le hB0 with hB_eq | h
      · exfalso
        have hzero : ∀ i, b i = 0 := by
          intro i
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 hB_eq.symm i
            (Finset.mem_univ i)
        have : A = 0 := by
          rw [hA]; exact Finset.sum_eq_zero fun i _ => hab i (hzero i)
        exact absurd this (ne_of_gt hApos)
      · exact h
    -- Pointwise bound on the summands.
    have key : ∀ i ∈ Finset.univ,
        a i - (A / B) * b i ≤ (a i * Real.log (a i) - a i * Real.log (b i))
          - (a i * Real.log A - a i * Real.log B) := by
      intro i _
      rcases eq_or_lt_of_le (ha i) with hai | hai
      · -- a i = 0
        have hai' : a i = 0 := hai.symm
        have hnn : 0 ≤ (A / B) * b i := mul_nonneg (div_nonneg hA0 hB0) (hb i)
        calc a i - (A / B) * b i ≤ 0 := by rw [hai']; linarith
          _ = (a i * Real.log (a i) - a i * Real.log (b i))
                - (a i * Real.log A - a i * Real.log B) := by simp [hai']
      · have hbi : 0 < b i := by
          rcases eq_or_lt_of_le (hb i) with h | h
          · exact absurd (hab i h.symm) (ne_of_gt hai)
          · exact h
        -- bracket = log ((a i * B) / (b i * A))
        have hx : 0 < (a i * B) / (b i * A) :=
          div_pos (mul_pos hai hBpos) (mul_pos hbi hApos)
        have hlog : Real.log ((a i * B) / (b i * A))
            = Real.log (a i) - Real.log (b i) - Real.log A + Real.log B := by
          rw [Real.log_div (ne_of_gt (mul_pos hai hBpos)) (ne_of_gt (mul_pos hbi hApos)),
            Real.log_mul (ne_of_gt hai) (ne_of_gt hBpos),
            Real.log_mul (ne_of_gt hbi) (ne_of_gt hApos)]
          ring
        have hineq := one_sub_inv_le_log hx
        rw [hlog] at hineq
        have hmul := mul_le_mul_of_nonneg_left hineq (le_of_lt hai)
        have hai0 : a i ≠ 0 := ne_of_gt hai
        have hbi0 : b i ≠ 0 := ne_of_gt hbi
        have hA0' : A ≠ 0 := ne_of_gt hApos
        have hB0' : B ≠ 0 := ne_of_gt hBpos
        have hinv : (a i) * ((a i * B) / (b i * A))⁻¹ = (A / B) * b i := by
          rw [inv_div]
          field_simp
        calc a i - (A / B) * b i
            = a i * (1 - ((a i * B) / (b i * A))⁻¹) := by rw [mul_sub, mul_one, hinv]
          _ ≤ a i * (Real.log (a i) - Real.log (b i) - Real.log A + Real.log B) := hmul
          _ = (a i * Real.log (a i) - a i * Real.log (b i))
                - (a i * Real.log A - a i * Real.log B) := by ring
    have hsum := Finset.sum_le_sum key
    have hleft : ∑ i, (a i - (A / B) * b i) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hA, ← hB]
      field_simp
      ring
    have hright : ∑ i, ((a i * Real.log (a i) - a i * Real.log (b i))
          - (a i * Real.log A - a i * Real.log B))
        = relEntropy a b - (A * Real.log A - A * Real.log B) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← hA]
    rw [hleft, hright] at hsum
    linarith

/-- Data-processing inequality for the KL divergence under a column-stochastic channel
`A : Y → I → ℝ`. -/
