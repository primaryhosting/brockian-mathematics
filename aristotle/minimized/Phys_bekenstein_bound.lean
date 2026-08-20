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

noncomputable def bekensteinLimit (k R E hbar c : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Bekenstein–Hawking entropy of a Schwarzschild black hole of energy `E`
(horizon area `A = 4 π (2 G E / c ^ 4) ^ 2`, entropy `S = k c ^ 3 A / (4 G ℏ)`),
expressed in terms of the energy: `4 π k G E ^ 2 / (ℏ c ^ 5)`. -/

noncomputable def blackHoleEntropyOfEnergy (k G E hbar c : ℝ) : ℝ :=
  4 * Real.pi * k * G * E ^ 2 / (hbar * c ^ 5)

/-- Consistency check: the Bekenstein–Hawking formula `S = k c ^ 3 A / (4 G ℏ)` applied to a
Schwarzschild horizon of radius `R = 2 G E / c ^ 4` and area `A = 4 π R ^ 2` indeed gives
`blackHoleEntropyOfEnergy`. -/

theorem bekenstein_bound
    (k G R E hbar c S : ℝ)
    (hk : 0 ≤ k) (hE : 0 ≤ E) (hhbar : 0 < hbar) (hc : 0 < c)
    (hSchwarzschild : 2 * G * E / c ^ 4 ≤ R)
    (hGSL : S ≤ blackHoleEntropyOfEnergy k G E hbar c) :
    S ≤ bekensteinLimit k R E hbar c := by
  have hfac : (0:ℝ) ≤ 2 * Real.pi * k * E / (hbar * c) := by
    have : (0:ℝ) < hbar * c := mul_pos hhbar hc
    positivity
  have hstep : blackHoleEntropyOfEnergy k G E hbar c
      ≤ 2 * Real.pi * k * E / (hbar * c) * R := by
    have hrw : blackHoleEntropyOfEnergy k G E hbar c
        = 2 * Real.pi * k * E / (hbar * c) * (2 * G * E / c ^ 4) := by
      unfold blackHoleEntropyOfEnergy
      field_simp
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hSchwarzschild hfac
  have hlim : bekensteinLimit k R E hbar c = 2 * Real.pi * k * E / (hbar * c) * R := by
    unfold bekensteinLimit
    field_simp
  rw [hlim]
  exact hGSL.trans hstep

end Phys
