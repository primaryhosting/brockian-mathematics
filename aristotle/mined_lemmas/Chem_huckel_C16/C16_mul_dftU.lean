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

/-!
# Hückel theory for the cyclic polyene C₁₆

The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of an annulene with
16 carbon atoms, up to the usual affine normalisation `α + β x`) has characteristic
polynomial `∏ k < 16, (X - 2 cos (2πk/16))`, so its eigenvalues are exactly the
numbers `2 cos (2πk/16)` for `k = 0, …, 15`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix
`U j k = ω^(jk)`, where `ω = exp (2πi/16)`.
-/

namespace Chem

open Polynomial Matrix Complex

/-- The adjacency (Hückel) matrix of the cycle graph `C₁₆`, over `ℂ`. -/

lemma C16_mul_dftU : C16 * dftU = dftU * Dg := by
  have hsucc : ∀ j : Fin 16, (j + 1 : Fin 16).val ≡ j.val + 1 [MOD 16] := by decide
  have hpred : ∀ j : Fin 16, (j - 1 : Fin 16).val ≡ j.val + 15 [MOD 16] := by decide
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ l : Fin 16, C16 j l * dftU l k
      = om ^ ((j + 1 : Fin 16).val * k.val) + om ^ ((j - 1 : Fin 16).val * k.val) := by
    simp only [C16_apply, dftU, Matrix.of_apply, add_mul, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_add_distrib]
    simp
  have hR : ∑ l : Fin 16, dftU j l * Dg l k
      = om ^ (j.val * k.val) * ((2 * Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ) := by
    simp only [dftU, Dg, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero]
    simp
  rw [hL, hR, two_cos_eq, mul_add, ← pow_add, ← pow_add]
  congr 1
  · exact om_pow_modEq (((hsucc j).mul_right k.val).trans (by rw [Nat.add_mul, one_mul]))
  · exact om_pow_modEq (((hpred j).mul_right k.val).trans (by rw [Nat.add_mul]))

/-- `dftU` as a unit of the matrix ring. -/
