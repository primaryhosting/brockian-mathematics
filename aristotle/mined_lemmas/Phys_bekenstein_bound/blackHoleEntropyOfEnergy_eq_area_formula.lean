/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

/-- The Bekenstein limit `2 π k R E / (ℏ c)`: the universal upper bound on the
thermodynamic entropy of a system of energy `E` contained in a sphere of radius `R`. -/

theorem blackHoleEntropyOfEnergy_eq_area_formula
    (k G E hbar c : ℝ) (hG : G ≠ 0) (hhbar : hbar ≠ 0) (hc : c ≠ 0) :
    k * c ^ 3 * (4 * Real.pi * (2 * G * E / c ^ 4) ^ 2) / (4 * G * hbar)
      = blackHoleEntropyOfEnergy k G E hbar c := by
  unfold blackHoleEntropyOfEnergy
  field_simp
  ring

/-- **The Bekenstein bound.**  For a physical system of energy `E ≥ 0` contained in a sphere of
radius `R`, the thermodynamic entropy `S` obeys `S ≤ 2 π k R E / (ℏ c)`.

The two physical inputs are Susskind's argument, which via the generalized second law bounds the
entropy of the system by the Bekenstein–Hawking entropy `4 π k G E ^ 2 / (ℏ c ^ 5)` of a black hole
of the same energy (`hGSL`), and the assumption that the system is not already inside its own
Schwarzschild radius, i.e. `2 G E / c ^ 4 ≤ R` (`hSchwarzschild`). -/
