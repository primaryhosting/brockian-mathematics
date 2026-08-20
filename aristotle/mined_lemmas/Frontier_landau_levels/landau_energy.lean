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

theorem landau_energy (m q B hbar b x0 k x : ℝ) (n : ℕ) (hm : m ≠ 0) (hq : q ≠ 0) (hB : B ≠ 0)
    (hhbar : hbar ≠ 0) (hb2 : b ^ 2 = 2 * q * B / hbar) (hx0 : x0 = hbar * k / (q * B)) :
    1 / (2 * m) * (-hbar ^ 2 * (b ^ 2 * ((b * (x - x0)) ^ 2 / 4 - 1 / 2 - n))
        + hbar ^ 2 * k ^ 2 - 2 * hbar * q * B * k * x + (q * B * x) ^ 2)
      = hbar * (q * B / m) * (n + 1 / 2) := by
  have hmul : (b * (x - x0)) ^ 2 = b ^ 2 * (x - x0) ^ 2 := by ring
  rw [hmul, hb2, hx0]
  field_simp
  ring

/-- **Landau levels.** A charged particle of mass `m` and charge `q` in a uniform magnetic
field `B` has energy spectrum `ℏ ω_c (n + 1/2)` with cyclotron frequency `ω_c = q B / m`:
the states `landauState` are eigenstates of the Landau Hamiltonian with these energies. -/
