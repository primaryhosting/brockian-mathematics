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

lemma zeta_twenty_mul (t : ℤ) : zeta (20 * t) = 1 := by
  have := Complex.exp_int_mul_two_pi_mul_I t
  rw [zeta]
  rw [show ((2 : ℂ) * Real.pi * Complex.I * ((20 * t : ℤ) : ℂ) / 20)
      = (t : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact this

