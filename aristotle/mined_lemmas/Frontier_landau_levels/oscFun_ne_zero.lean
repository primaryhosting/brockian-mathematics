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

namespace Frontier

open Polynomial

/-! ## Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials, defined by `H₀ = 1` and
`H_{n+1} = 2X H_n - H_n'`. -/

theorem oscFun_ne_zero (n : ℕ) : ∃ t : ℝ, oscFun n t ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine hermiteP_ne_zero n (Polynomial.funext fun r => ?_)
  have h := hcon r
  simp only [oscFun, gfun, mul_eq_zero] at h
  rcases h with h | h
  · simpa using h
  · exact absurd h (Real.exp_ne_zero _)

/-! ## Landau levels -/

/-- Kinetic momentum operator in the `x` direction, `π_x = -iℏ ∂_x`. -/
