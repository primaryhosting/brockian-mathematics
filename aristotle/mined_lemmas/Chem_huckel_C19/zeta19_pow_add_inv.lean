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

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma zeta19_pow_add_inv (k : ℕ) :
    zeta19 ^ k + (zeta19 ^ k)⁻¹ = lam19 k := by
  have hk : zeta19 ^ k = Complex.exp (((2 * Real.pi * k / 19 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta19, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hk, ← Complex.exp_neg, lam19, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  rw [neg_mul]
  ring

/-- The discrete Fourier matrix. -/
