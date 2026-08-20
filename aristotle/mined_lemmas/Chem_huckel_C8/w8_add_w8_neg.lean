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

theorem w8_add_w8_neg (k : Fin 8) :
    w8 k + w8 (-k) = ((huckelEigenvalue k : ℝ) : ℂ) := by
  have h1 : w8 k = Complex.exp ((2 * Real.pi * k.val / 8 : ℝ) * Complex.I) := by
    rw [w8, zeta8, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : w8 (-k) = Complex.exp (-((2 * Real.pi * k.val / 8 : ℝ) * Complex.I)) := by
    rw [w8_neg, h1, ← Complex.exp_neg]
  rw [h1, h2, huckelEigenvalue, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-! ### Diagonalisation -/

/-- The columns of the discrete Fourier matrix are eigenvectors of the adjacency matrix. -/
