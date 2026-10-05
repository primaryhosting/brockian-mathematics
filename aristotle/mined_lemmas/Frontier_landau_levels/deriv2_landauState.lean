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

open Polynomial

namespace Frontier

/-! ### Hermite polynomial facts -/

/-- The derivative of the `(n+1)`-st probabilists' Hermite polynomial. -/

theorem deriv2_landauState {hbar m omegac : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hw : 0 < omegac)
    (n : ℕ) (y : ℝ) :
    deriv (deriv (landauState hbar m omegac n)) y
      = (1 / (landauLength hbar m omegac) ^ 2) *
        (((y / landauLength hbar m omegac) ^ 2 / 4 - ((n : ℝ) + 1 / 2)) *
          landauState hbar m omegac n y) := by
  have hl : landauLength hbar m omegac ≠ 0 := ne_of_gt (landauLength_pos hh hm hw)
  rw [deriv_landauState hbar m omegac n]
  have hin : HasDerivAt (fun z : ℝ => z / landauLength hbar m omegac)
      (1 / landauLength hbar m omegac) y := by
    simpa using (hasDerivAt_id y).div_const (landauLength hbar m omegac)
  have h := ((hasDerivAt_hermiteGauss' n (y / landauLength hbar m omegac)).comp y hin).const_mul
    (1 / landauLength hbar m omegac)
  refine (h.congr_deriv ?_).deriv
  simp only [landauState]
  field_simp

/-- **Landau levels.**  A charged particle in a uniform magnetic field, reduced (in the Landau
gauge) to the one-dimensional Hamiltonian `H = -ħ²/(2m) d²/dy² + ½ m ω_c² y²` with cyclotron
frequency `ω_c`, has the Hermite–Gauss functions `landauState` as eigenfunctions, with
eigenvalues the Landau levels `E_n = ħ ω_c (n + ½)`. -/
