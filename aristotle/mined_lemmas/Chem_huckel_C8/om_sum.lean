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

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma om_sum (k : ℕ) : om ^ k + om ^ (7 * k) = ((2 * Real.cos (2 * Real.pi * k / 8) : ℝ) : ℂ) := by
  set x : ℂ := ((2 * Real.pi * k / 8 : ℝ) : ℂ) with hx
  have h1 : om ^ k = Complex.exp (x * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul, hx]
    congr 1
    push_cast; ring
  have hk : om ^ k ≠ 0 := by rw [h1]; exact Complex.exp_ne_zero _
  have h2 : om ^ (7 * k) = Complex.exp (-(x * Complex.I)) := by
    have e1 : om ^ (7 * k) * om ^ k = 1 := by
      rw [← pow_add, show 7 * k + k = 8 * k by ring, pow_mul, om_pow_eight, one_pow]
    have e2 : Complex.exp (-(x * Complex.I)) * om ^ k = 1 := by
      rw [h1, ← Complex.exp_add]; simp
    exact mul_right_cancel₀ hk (e1.trans e2.symm)
  rw [h1, h2, Complex.exp_mul_I, show -(x * Complex.I) = (-x) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, hx]
  push_cast
  ring

/-- The Fourier (Vandermonde) matrix of the eighth roots of unity. -/
