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

lemma U_mul_V : U * V = (20 : ℂ) • (1 : Matrix (Fin 20) (Fin 20) ℂ) := by
  ext i k
  have : (U * V) i k = ∑ j : Fin 20, zeta ((j : ℕ) * (((i : ℕ) : ℤ) - (k : ℕ))) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [U, V, ← zeta_add]
    congr 1
    ring
  rw [this, geom_sum_zeta]
  by_cases hik : i = k
  · subst hik
    simp
  · have : ¬ ((20 : ℤ) ∣ (((i : ℕ) : ℤ) - (k : ℕ))) := by
      have hi := i.isLt
      have hk := k.isLt
      have : (i : ℕ) ≠ (k : ℕ) := fun hc => hik (Fin.ext hc)
      omega
    simp [this, Matrix.one_apply_ne hik]

