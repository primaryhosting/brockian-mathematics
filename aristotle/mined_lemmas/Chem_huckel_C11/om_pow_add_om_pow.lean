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

open Polynomial Matrix SimpleGraph

/-! ## Hückel theory for the cycle `C₁₁`

We compute the spectrum of the adjacency matrix of the cycle graph on 11 vertices by
diagonalising it with the discrete Fourier transform matrix. -/

/-- A primitive 11-th root of unity. -/

lemma om_pow_add_om_pow (l : ℕ) :
    om ^ l + om ^ (10 * l) = ((2 * Real.cos (2 * Real.pi * l / 11) : ℝ) : ℂ) := by
  rw [om_pow_eq_exp, om_pow_eq_exp]
  push_cast
  rw [Complex.two_cos]
  have h : 2 * (Real.pi : ℂ) * (10 * l) / 11 * Complex.I
      = (l : ℂ) * (2 * Real.pi * Complex.I) + -(2 * (Real.pi : ℂ) * l / 11) * Complex.I := by
    ring
  rw [h, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]

/-- The sum of all 11-th powers of a nontrivial 11-th root of unity vanishes. -/
