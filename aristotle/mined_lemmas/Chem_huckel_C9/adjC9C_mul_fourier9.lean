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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ## The adjacency matrix of the cycle graph `C₉` -/

/-- The adjacency matrix of the cycle graph `C₉`, i.e. the Hückel matrix of the
cyclononatetraenyl π-system with `α = 0` and `β = 1`. -/

lemma adjC9C_mul_fourier9 : adjC9C * fourier9 = fourier9 * diagC9 := by
  ext i k
  have hz9 : (w9 ^ (k : ℕ)) ^ 9 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, w9_pow_nine, one_pow]
  have hcol : ∀ j : Fin 9, fourier9 j k = (w9 ^ (k : ℕ)) ^ (j : ℕ) := by
    intro j
    rw [fourier9, Matrix.vandermonde_apply, ← pow_mul, ← pow_mul, mul_comm]
  rw [Matrix.mul_apply, diagC9, Matrix.mul_diagonal]
  calc ∑ j : Fin 9, adjC9C i j * fourier9 j k
      = ∑ j : Fin 9, adjC9C i j * (w9 ^ (k : ℕ)) ^ (j : ℕ) := by
        exact Finset.sum_congr rfl (fun j _ => by rw [hcol j])
    _ = (w9 ^ (k : ℕ)) ^ ((i + 1 : Fin 9) : ℕ) + (w9 ^ (k : ℕ)) ^ ((i - 1 : Fin 9) : ℕ) :=
        adjC9C_row_sum i _
    _ = (w9 ^ (k : ℕ)) ^ (i : ℕ) * (w9 ^ (k : ℕ) + (w9 ^ (k : ℕ))⁻¹) :=
        pow_shift_identity hz9 i
    _ = fourier9 i k * ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ) := by
        rw [hcol i, w9_pow_add_inv]

