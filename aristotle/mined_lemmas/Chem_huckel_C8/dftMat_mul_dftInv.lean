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

theorem dftMat_mul_dftInv : dftMat * dftInv = 1 := by
  have hmul : ∀ i k j : Fin 8, i * j + -(j * k) = j * (i - k) := by decide
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 8, dftMat i j * dftInv j k = (8 : ℂ)⁻¹ * w8 (j * (i - k)) := by
    intro j
    rw [dftMat, dftInv]
    simp only [Matrix.of_apply]
    rw [← hmul i k j, w8_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_w8]
  by_cases h : i = k
  · subst h
    simp
  · rw [if_neg (by simpa [sub_eq_zero] using h), Matrix.one_apply_ne h, mul_zero]

/-- The discrete Fourier matrix, as a unit of the matrix ring. -/
