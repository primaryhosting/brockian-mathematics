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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
# Landau levels

A charged particle of mass `m` and charge `q` moving in the plane in a uniform magnetic field `B`
perpendicular to the plane has energy spectrum `ℏ ω_c (n + 1/2)`, where `ω_c = q B / m` is the
cyclotron frequency.

We work in the Landau gauge `A = (0, B x)`, so that the Hamiltonian is

  `H = (1/(2m)) ( (-iℏ ∂ₓ)² + (-iℏ ∂_y - q B x)² )`
    `= (1/(2m)) ( -ℏ² ∂ₓ² - ℏ² ∂_y² + 2iℏ q B x ∂_y + q²B²x² )`,

which is `Frontier.landauH` below.

The eigenfunctions are `exp (i k y)` times a shifted Hermite function of `x`
(`Frontier.landauState`), and `Frontier.landau_levels` states that these are eigenfunctions of
`landauH` with eigenvalue `ℏ (qB/m) (n + 1/2)`.
-/

namespace Frontier

open Polynomial

/-! ### Hermite polynomial preliminaries -/

/-- The derivative of the (probabilists') Hermite polynomial: `He_{n+1}' = (n+1) He_n`. -/

theorem landauH_hermiteState (m q B hbar b x0 k : ℝ) (n : ℕ) (x y : ℝ) :
    landauH m q B hbar
        (fun s t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) *
          ((hFun n (b * (s - x0)) : ℝ) : ℂ)) x y
      = ((1 / (2 * m) * (-hbar ^ 2 * (b ^ 2 * ((b * (x - x0)) ^ 2 / 4 - 1 / 2 - n))
            + hbar ^ 2 * k ^ 2 - 2 * hbar * q * B * k * x + (q * B * x) ^ 2) : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)) := by
  have hinner : ∀ t : ℝ, HasDerivAt (fun s : ℝ => b * (s - x0)) b t := by
    intro t
    simpa using ((hasDerivAt_id t).sub_const x0).const_mul b
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => hFun n (b * (s - x0)))
      (b * dhFun n (b * (t - x0))) t := by
    intro t
    simpa [mul_comm] using (hasDerivAt_hFun n (b * (t - x0))).comp t (hinner t)
  have hdF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => b * dhFun n (b * (s - x0)))
      (b ^ 2 * ((b * (t - x0)) ^ 2 / 4 - 1 / 2 - n) * hFun n (b * (t - x0))) t := by
    intro t
    have h := ((hasDerivAt_dhFun n (b * (t - x0))).comp t (hinner t)).const_mul b
    refine h.congr_deriv ?_
    ring
  -- derivatives in the `x` direction
  have hx1 : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (s - x0)) : ℝ) : ℂ))
      (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((b * dhFun n (b * (t - x0)) : ℝ) : ℂ)) t :=
    fun t => ((hF t).ofReal_comp).const_mul _
  have hx1' : (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (s - x0)) : ℝ) : ℂ))
      = fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((b * dhFun n (b * (t - x0)) : ℝ) : ℂ) :=
    funext fun t => (hx1 t).deriv
  have hx2 : deriv (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (s - x0)) : ℝ) : ℂ)) x
      = Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((b ^ 2 * ((b * (x - x0)) ^ 2 / 4 - 1 / 2 - n) * hFun n (b * (x - x0)) : ℝ) : ℂ) := by
    rw [hx1']
    exact (((hdF x).ofReal_comp).const_mul _).deriv
  -- derivatives in the `y` direction
  have hexp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)))
      (Complex.I * (k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (t : ℂ))) t := by
    intro t
    have h : HasDerivAt (fun s : ℝ => Complex.I * (k : ℂ) * ((s : ℝ) : ℂ))
        (Complex.I * (k : ℂ)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (k : ℂ))
    simpa [mul_comm] using h.cexp
  have hy1' : (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ))
      = fun t : ℝ => Complex.I * (k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) *
          ((hFun n (b * (x - x0)) : ℝ) : ℂ) :=
    funext fun t => ((hexp t).mul_const _).deriv
  have hy2 : deriv (deriv fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)) y
      = (Complex.I * (k : ℂ)) ^ 2 * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((hFun n (b * (x - x0)) : ℝ) : ℂ) := by
    rw [hy1']
    have h := (((hexp y).const_mul (Complex.I * (k : ℂ))).mul_const
      (((hFun n (b * (x - x0)) : ℝ) : ℂ))).deriv
    rw [h]
    ring
  have hy1 : deriv (fun s : ℝ =>
        Complex.exp (Complex.I * (k : ℂ) * (s : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)) y
      = Complex.I * (k : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) *
          ((hFun n (b * (x - x0)) : ℝ) : ℂ) := by
    rw [hy1']
  simp only [landauH, hx2, hy2, hy1]
  push_cast
  linear_combination ((1 / (2 * (m : ℂ))) * (-(hbar : ℂ) ^ 2 * (k : ℂ) ^ 2
      + 2 * (hbar : ℂ) * (q : ℂ) * (B : ℂ) * (x : ℂ) * (k : ℂ))
      * (Complex.exp (Complex.I * (k : ℂ) * (y : ℂ)) * ((hFun n (b * (x - x0)) : ℝ) : ℂ)))
    * Complex.I_sq

/-- The energy coefficient collapses to `ℏ ω_c (n + 1/2)`. -/
