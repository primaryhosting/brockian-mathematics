/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15

Category: Chemistry.  Target: `Chem.huckel_C15`.

The Hückel (adjacency) eigenvalues of the cycle graph `C₁₅` are `2 cos (2πk/15)`, `k = 0, …, 14`.

The proof diagonalizes the adjacency matrix by the discrete Fourier matrix
`U i k = ζ ^ (k * i)` with `ζ = exp (2πi/15)`, and then uses
`spectrum.units_conjugate` together with `spectrum_diagonal`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/

theorem dftMatrix_mul_inv : dftMatrix * dftMatrixInv = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  set w : ℂ := zeta ^ i.val * (zeta⁻¹) ^ j.val with hw
  have hterm : ∀ k : Fin 15, dftMatrix i k * dftMatrixInv k j = (15 : ℂ)⁻¹ * w ^ k.val := by
    intro k
    simp only [dftMatrix, dftMatrixInv, hw]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  have hwpow : w ^ 15 = 1 := by
    rw [hw, mul_pow, zeta_pow_pow_fifteen, inv_pow, inv_pow, zeta_pow_pow_fifteen, inv_one, mul_one]
  have hsum : ∑ k : Fin 15, w ^ k.val = if i = j then 15 else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k)]
    by_cases hij : i = j
    · subst hij
      have hw1 : w = 1 := by
        rw [hw, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ zeta_ne_zero)]
      simp [hw1]
    · have hwne : w ≠ 1 := by
        rw [hw, inv_pow]
        intro h
        rw [mul_inv_eq_one₀ (pow_ne_zero _ zeta_ne_zero), zeta_pow_eq_iff] at h
        exact hij (Fin.ext (by
          have := i.isLt; have := j.isLt; unfold Nat.ModEq at h; omega))
      rw [geom_sum_eq hwne, hwpow, if_neg hij]
      simp
  rw [hsum]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, Matrix.one_apply_eq]; norm_num
  · rw [if_neg hij, Matrix.one_apply_ne hij, mul_zero]

