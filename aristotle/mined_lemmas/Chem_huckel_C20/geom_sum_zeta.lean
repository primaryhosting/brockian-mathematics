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
# Hückel theory for the cycle C₂₀

The adjacency eigenvalues of the cycle graph `C₂₀` are `2 * cos (2 π k / 20)`, `k = 0, …, 19`.

We prove this by explicitly diagonalizing the adjacency matrix with the discrete Fourier
transform matrix `U i k = ζ (i * k)`, where `ζ m = exp (2 π i m / 20)`.
-/

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- `ζ m = exp (2 π i m / 20)`, a 20-th root of unity raised to the power `m`. -/

lemma geom_sum_zeta (m : ℤ) :
    ∑ j : Fin 20, zeta ((j : ℕ) * m) = if (20 : ℤ) ∣ m then 20 else 0 := by
  have hpow : ∀ j : Fin 20, zeta ((j : ℕ) * m) = zeta m ^ (j : ℕ) := fun j =>
    zeta_natCast_mul (j : ℕ) m
  simp only [hpow]
  rw [Fin.sum_univ_eq_sum_range (fun n => zeta m ^ n) 20]
  by_cases h : (20 : ℤ) ∣ m
  · have : zeta m = 1 := zeta_eq_one_iff.mpr h
    simp [this, h]
  · have hne : zeta m ≠ 1 := fun hc => h (zeta_eq_one_iff.mp hc)
    have h20 : zeta m ^ (20 : ℕ) = 1 := by
      rw [← zeta_natCast_mul 20 m]
      exact zeta_twenty_mul m
    rw [geom_sum_eq hne, h20]
    simp [h]

