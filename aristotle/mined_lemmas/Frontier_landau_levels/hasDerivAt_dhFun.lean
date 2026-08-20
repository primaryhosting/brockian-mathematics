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

theorem hasDerivAt_dhFun (n : ℕ) (y : ℝ) :
    HasDerivAt (dhFun n) ((y ^ 2 / 4 - 1 / 2 - n) * hFun n y) y := by
  have hd : HasDerivAt (fun t : ℝ => He1 n t - t / 2 * He n t)
      (He2 n y - (1 / 2 * He n y + y / 2 * He1 n y)) y := by
    have h1 := hasDerivAt_He1 n y
    have h2 := ((hasDerivAt_id y).div_const 2).mul (hasDerivAt_He n y)
    simpa using h1.sub h2
  have h := hd.mul (hasDerivAt_gaussian y)
  refine h.congr_deriv ?_
  have hode := He_ode n y
  simp only [hFun]
  nlinarith [hode, Real.exp_pos (-(y ^ 2) / 4)]

/-! ### The Landau Hamiltonian -/

/-- The Landau Hamiltonian in the Landau gauge `A = (0, B x)`:
`H ψ = (1/(2m)) ( -ℏ² ∂ₓ²ψ - ℏ² ∂_y²ψ + 2iℏ q B x ∂_yψ + q²B²x² ψ )`. -/
