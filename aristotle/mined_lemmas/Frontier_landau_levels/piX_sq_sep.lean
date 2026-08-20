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

theorem piX_sq_sep (hbar k : ℝ) (f f' f'' : ℝ → ℝ) (h1 : ∀ x, HasDerivAt f (f' x) x)
    (h2 : ∀ x, HasDerivAt f' (f'' x) x) :
    piX hbar (piX hbar (fun x y : ℝ => Complex.exp (Complex.I * k * y) * (f x : ℂ)))
      = fun x y : ℝ => ((-hbar ^ 2 : ℝ) : ℂ) * (Complex.exp (Complex.I * k * y) * (f'' x : ℂ)) := by
  rw [piX_sep hbar k f f' h1]
  funext x y
  have hd : deriv (fun s : ℝ =>
      -Complex.I * hbar * (Complex.exp (Complex.I * k * y) * (f' s : ℂ))) x
      = -Complex.I * hbar * (Complex.exp (Complex.I * k * y) * (f'' x : ℂ)) :=
    ((((h2 x).ofReal_comp).const_mul (Complex.exp (Complex.I * k * y))).const_mul
      (-Complex.I * (hbar : ℂ))).deriv
  simp only [piX, hd]
  push_cast
  linear_combination ((hbar : ℂ) ^ 2 * Complex.exp (Complex.I * k * y) * (f'' x : ℂ)) * Complex.I_sq

/-- The Hamiltonian of a particle of mass `m` and charge `q` in a uniform magnetic field `B`
perpendicular to the plane, in the Landau gauge: `H = (π_x² + π_y²)/(2m)`. -/
