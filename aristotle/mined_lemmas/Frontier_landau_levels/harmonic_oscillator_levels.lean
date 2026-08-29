/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the same text is repeated below as the module docstring.)

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Polynomial

/-! ### Hermite polynomials: the Hermite differential equation

Mathlib provides `Polynomial.hermite : ℕ → ℤ[X]` (the *probabilists'* Hermite polynomials)
together with `Polynomial.hermite_succ`, but not the Hermite ODE, which we derive here. -/

/-- The Hermite differential equation `He_n'' = X * He_n' - n * He_n`. -/

theorem harmonic_oscillator_levels (hbar m om x0 : ℝ) (hh : 0 < hbar) (hm : 0 < m) (ho : 0 < om)
    (n : ℕ) (ell : ℝ) (hell : ell = Real.sqrt (hbar / (m * om)))
    (psi : ℝ → ℝ)
    (hpsi : ∀ x, psi x = Polynomial.aeval (Real.sqrt 2 * (x - x0) / ell) (hermite n)
      * Real.exp (-((x - x0) ^ 2 / (2 * ell ^ 2)))) (x : ℝ) :
    -(hbar ^ 2 / (2 * m)) * deriv (deriv psi) x + (1 / 2) * m * om ^ 2 * (x - x0) ^ 2 * psi x
      = hbar * om * (n + 1 / 2) * psi x := by
  have hb := psi_eq_polyGauss hbar m om x0 hh hm ho n ell hell psi hpsi
  obtain ⟨a, b, ha, hab, hbval, hfun⟩ := hb
  rw [hfun, polyGauss_second_deriv (hermiteR n) (n : ℝ) a b x0 ha hab (hermiteR_ode n) x, hbval]
  have hne : hbar ≠ 0 := ne_of_gt hh
  have hmne : m ≠ 0 := ne_of_gt hm
  field_simp
  ring

/-! ### Landau levels: a charged particle in a uniform magnetic field -/

/-- **Landau levels.**  A particle of mass `m` and charge `q > 0` in a uniform magnetic field
`B ẑ`, described in the Landau gauge `A = (0, B x, 0)`, has Hamiltonian
`H = (π_x² + π_y²)/(2m)` with kinetic momenta `π_x = -iħ ∂_x` and `π_y = -iħ ∂_y - q B x`.
For every `n : ℕ` and every transverse wavenumber `k`, the state
`Ψ(x,y) = e^{i k y} · He_n(√2 (x-x₀)/ℓ) · e^{-(x-x₀)²/(2ℓ²)}`,
with guiding centre `x₀ = ħk/(qB)` and magnetic length `ℓ = √(ħ/(m ω_c))`,
is an eigenstate of `H` with energy `ħ ω_c (n + ½)`, where `ω_c = qB/m` is the cyclotron
frequency.  Thus the energy spectrum consists of the Landau levels `ħ ω_c (n + ½)`. -/
