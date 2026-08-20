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

noncomputable def landauPsi (hbar q B : ℝ) (n : ℕ) (k : ℝ) : ℝ → ℝ → ℂ :=
  fun x y => Complex.exp (Complex.I * k * y) *
    (oscFun n (Real.sqrt (q * B / hbar) * (x - hbar * k / (q * B))) : ℝ)

/-- The algebraic identity behind the Landau spectrum: with `C² = Q/H` (i.e. `C = √(qB/ℏ)`),
the oscillator potential and the Gaussian curvature term combine to the constant
`H (Q/M) (N + 1/2)`. -/
