/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

noncomputable section

open Polynomial

/-! ## Probabilists' Hermite polynomials over `ℝ` -/

/-- The `n`-th probabilists' Hermite polynomial, with real coefficients. -/

theorem landau_energy_algebra (hbar m c k x G nn : ℝ) (hc : c ≠ 0) (hm : m ≠ 0)
    (hhb : hbar ≠ 0) :
    -(hbar ^ 2) * (((x - hbar * k / c) ^ 2 / (4 * (hbar / (2 * c)) ^ 2)
        - (nn + 1 / 2) / (hbar / (2 * c))) * G)
      + (hbar * k - c * x) ^ 2 * G
      = 2 * m * (hbar * (c / m) * (nn + 1 / 2) * G) := by
  field_simp
  ring

/-- **Landau levels.** For a particle of mass `m > 0` and charge `q` moving in the plane in a
uniform perpendicular magnetic field `B` (with `qB > 0`), the Landau-gauge Hamiltonian
`H = ((-iℏ∂ₓ)² + (-iℏ∂_y - qBx)²)/(2m)` has the orbitals
`ψ_{n,k}(x,y) = e^{iky} He_n((x-x₀)/s) e^{-(x-x₀)²/(4s²)}` as eigenfunctions, with the
Landau-level energies `E_n = ℏ ω_c (n + 1/2)`, where `ω_c = qB/m` is the cyclotron frequency,
`s = √(ℏ/(2qB))` is the magnetic length and `x₀ = ℏk/(qB)` is the guiding centre. -/
