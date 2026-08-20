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

lemma lam_eq (k : Fin 20) : lam k = zeta (k : ℕ) + zeta (-(k : ℕ)) := by
  have h1 : zeta ((k : ℕ) : ℤ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 20 : ℝ) * Complex.I) := by
    rw [zeta]; congr 1; push_cast; ring
  have h2 : zeta (-((k : ℕ) : ℤ)) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta]; congr 1; push_cast; ring
  rw [lam, h1, h2, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- Fin-valued addition is compatible with `zeta`'s argument modulo 20. -/
