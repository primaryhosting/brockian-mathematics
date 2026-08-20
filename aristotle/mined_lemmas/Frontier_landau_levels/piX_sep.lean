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

theorem piX_sep (hbar k : ℝ) (f f' : ℝ → ℝ) (h : ∀ x, HasDerivAt f (f' x) x) :
    piX hbar (fun x y : ℝ => Complex.exp (Complex.I * k * y) * (f x : ℂ))
      = fun x y : ℝ => -Complex.I * hbar * (Complex.exp (Complex.I * k * y) * (f' x : ℂ)) := by
  funext x y
  have hd : deriv (fun s : ℝ => Complex.exp (Complex.I * k * y) * (f s : ℂ)) x
      = Complex.exp (Complex.I * k * y) * (f' x : ℂ) :=
    (((h x).ofReal_comp).const_mul (Complex.exp (Complex.I * k * y))).deriv
  simp only [piX, hd]

/-- `π_x²` acts on a separated state as `-ℏ² ∂_x²`. -/
