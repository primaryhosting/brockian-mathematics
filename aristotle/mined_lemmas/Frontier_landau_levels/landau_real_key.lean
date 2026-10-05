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

open Polynomial

/-! ## Hermite polynomials over `ℝ` -/

/-- The (probabilists') Hermite polynomials, with real coefficients. -/

theorem landau_real_key (hm : 0 < m) (hhbar : 0 < hbar) (hqB : 0 < q * B) (x : ℝ) :
    (1 / (2 * m)) * (-(hbar ^ 2) * ddphiR hbar q B k n x
        + (hbar * k - q * B * x) ^ 2 * phiR hbar q B k n x)
      = hbar * (q * B / m) * (n + 1 / 2) * phiR hbar q B k n x := by
  have hL : landauL hbar q B ≠ 0 := (landauL_pos hhbar hqB).ne'
  have hL2 : landauL hbar q B ^ 2 = hbar / (2 * (q * B)) := landauL_sq hhbar hqB
  have hh0 : hbar ≠ 0 := hhbar.ne'
  have hqB0 : q * B ≠ 0 := hqB.ne'
  have hq0 : q ≠ 0 := fun h => hqB0 (by simp [h])
  have hB0 : B ≠ 0 := fun h => hqB0 (by simp [h])
  have hm0 : m ≠ 0 := hm.ne'
  have hA : (1 / landauL hbar q B) ^ 2 = 2 * (q * B) / hbar := by
    rw [div_pow, one_pow, hL2]
    field_simp
  have hBsq : ((x - landauX0 hbar q B k) / landauL hbar q B) ^ 2
      = (x - landauX0 hbar q B k) ^ 2 * (2 * (q * B) / hbar) := by
    rw [div_pow, hL2]
    field_simp
  have hscalar : (1 / (2 * m)) * (-(hbar ^ 2) * ((1 / landauL hbar q B) ^ 2 *
        (((x - landauX0 hbar q B k) / landauL hbar q B) ^ 2 / 4 - ((n : ℝ) + 1 / 2)))
        + (hbar * k - q * B * x) ^ 2)
      = hbar * (q * B / m) * ((n : ℝ) + 1 / 2) := by
    rw [hA, hBsq, landauX0]
    field_simp
    ring
  simp only [ddphiR, chi2_eq, phiR]
  linear_combination (chi n ((x - landauX0 hbar q B k) / landauL hbar q B)) * hscalar

end

/-- **Landau levels.**  A charged particle of mass `m > 0` and charge `q` moving in the plane
in a uniform perpendicular magnetic field `B` (with `qB > 0`), described in the Landau gauge
by the Hamiltonian `H = ((-iℏ∂_x)² + (-iℏ∂_y - qBx)²)/(2m)`, has, for every `n : ℕ` and every
transverse wavenumber `k`, an eigenfunction `landauPsi` with eigenvalue `ℏ ω_c (n + 1/2)`,
where `ω_c = qB/m` is the cyclotron frequency. -/
