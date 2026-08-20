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

theorem hermiteP_ne_zero (n : ℕ) : hermiteP n ≠ 0 := by
  intro h
  have hco := (hermiteP_deg_coeff n).2
  rw [h] at hco
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  simp only [Polynomial.coeff_zero] at hco
  linarith

/-! ## Gaussian-damped polynomials and the harmonic-oscillator eigenfunctions -/

/-- `gfun p t = p(t) e^{-t²/2}`. -/
