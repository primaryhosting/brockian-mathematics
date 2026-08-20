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

lemma om_pow_eight : om ^ 8 = 1 := by
  rw [om, ← Complex.exp_nat_mul,
    show ((8 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 8) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I]
  norm_cast
  simp

