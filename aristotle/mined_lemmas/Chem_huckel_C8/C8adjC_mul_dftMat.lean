import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial

/-- A primitive 8-th root of unity. -/

theorem C8adjC_mul_dftMat : C8adjC * dftMat = dftMat * eigDiag := by
  have hne : ∀ i : Fin 8, i - 1 ≠ i + 1 := by decide
  have hchar : ∀ i l : Fin 8, (i - l = 1 → l = i - 1) ∧ (i - l = -1 → l = i + 1) := by decide
  have hd1 : ∀ i : Fin 8, i - (i - 1) = 1 := by decide
  have hd2 : ∀ i : Fin 8, i - (i + 1) = -1 := by decide
  have hmul1 : ∀ i j : Fin 8, (i - 1) * j = i * j + (-j) := by decide
  have hmul2 : ∀ i j : Fin 8, (i + 1) * j = i * j + j := by decide
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hrhs : (∑ l : Fin 8, dftMat i l * eigDiag l j)
      = w8 (i * j) * ((huckelEigenvalue j : ℝ) : ℂ) := by
    simp [eigDiag, Matrix.diagonal_apply, dftMat, eq_comm]
  rw [hrhs]
  have hlhs : ∀ l : Fin 8, C8adjC i l * dftMat l j
      = (if i - l = 1 ∨ i - l = -1 then (1 : ℂ) else 0) * w8 (l * j) := by
    intro l
    rw [C8adjC_apply, dftMat]
    rfl
  rw [Finset.sum_congr rfl (fun l _ => hlhs l),
    Finset.sum_eq_add_of_mem (i - 1) (i + 1) (Finset.mem_univ _) (Finset.mem_univ _) (hne i)
      (by
        intro c _ hc
        rw [if_neg, zero_mul]
        rintro (h | h)
        · exact hc.1 ((hchar i c).1 h)
        · exact hc.2 ((hchar i c).2 h)),
    if_pos (Or.inl (hd1 i)), if_pos (Or.inr (hd2 i)), one_mul, one_mul,
    hmul1 i j, hmul2 i j, w8_add, w8_add, ← mul_add, add_comm (w8 (-j)) (w8 j), w8_add_w8_neg]

