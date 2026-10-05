import Mathlib
import RequestProject.Classical

/-!
# Quantum relative entropy

Definitions of the matrix logarithm (via the continuous functional calculus), the Umegaki
relative entropy of two density matrices, and quantum channels in Kraus form.
-/

open Matrix Unitary
open scoped BigOperators ComplexOrder

namespace QI

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι]

/-- The matrix logarithm of a Hermitian matrix, defined through the continuous functional
calculus (with the convention `log 0 = 0`, so that vanishing eigenvalues contribute nothing). -/

theorem log_sum_le [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * (Real.log (∑ i, a i) - Real.log (∑ i, b i))
      ≤ ∑ i, a i * (Real.log (a i) - Real.log (b i)) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hs : ∑ i, a i = 0 := by rw [← hA]; exact hA0'.symm
    have hzero : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 hs i (Finset.mem_univ i)
    simp [hzero, ← hA0']
  · have hBpos : 0 < B := by
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ B from Finset.sum_nonneg fun i _ => hb i) with h | h
      · exfalso
        have hs : ∑ i, b i = 0 := by rw [← hB]; exact h.symm
        have hb0 : ∀ i, b i = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 hs i (Finset.mem_univ i)
        have hz : ∀ i, a i = 0 := fun i => hab i (hb0 i)
        rw [hA] at hApos
        simp [hz] at hApos
      · exact h
    have key : ∀ i, a i * (Real.log A - Real.log B) + (a i - b i * (A / B))
        ≤ a i * (Real.log (a i) - Real.log (b i)) := by
      intro i
      rcases eq_or_lt_of_le (ha i) with hai | hai
      · have hbi : 0 ≤ b i * (A / B) := mul_nonneg (hb i) (by positivity)
        rw [← hai]
        simp
        linarith
      · have hbi : 0 < b i := by
          rcases eq_or_lt_of_le (hb i) with h | h
          · exact absurd (hab i h.symm) (by linarith)
          · exact h
        have ht : 0 < b i * A / (a i * B) := by positivity
        have hlog := Real.log_le_sub_one_of_pos ht
        have hlogeq : Real.log (b i * A / (a i * B))
            = Real.log (b i) + Real.log A - Real.log (a i) - Real.log B := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
            (by positivity), Real.log_mul (by positivity) (by positivity)]
          ring
        rw [hlogeq] at hlog
        have hkey : a i * (Real.log (a i) - Real.log (b i) - (Real.log A - Real.log B))
            ≥ a i * (1 - b i * A / (a i * B)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hai)
          linarith
        have h2 : a i * (1 - b i * A / (a i * B)) = a i - b i * (A / B) := by
          field_simp
        rw [h2] at hkey
        nlinarith [hkey]
    have hsum : ∑ i, (a i * (Real.log A - Real.log B) + (a i - b i * (A / B)))
        = A * (Real.log A - Real.log B) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hA, ← hB]
      field_simp
      ring
    calc A * (Real.log A - Real.log B)
        = ∑ i, (a i * (Real.log A - Real.log B) + (a i - b i * (A / B))) := hsum.symm
      _ ≤ ∑ i, a i * (Real.log (a i) - Real.log (b i)) := Finset.sum_le_sum fun i _ => key i

/-- **Classical data-processing inequality**: the Kullback–Leibler divergence is monotone
under (column-)stochastic maps. -/
