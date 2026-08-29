import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Pointwise

namespace Chem

/-- The intensive state variables of a system with `C` chemical components distributed over
`P` phases: temperature, pressure, and the `C` mole fractions of each of the `P` phases,
i.e. `2 + P * C` real variables. -/
abbrev StateVars (C P : ℕ) : Type := Fin (2 + P * C) → ℝ

/-- The equilibrium constraints on the intensive variables: one normalization condition
`∑ mole fractions = 1` per phase (`P` equations) together with the equality of the chemical
potential of each component across consecutive phases (`C * (P - 1)` equations). -/
abbrev Constraints (C P : ℕ) : Type := Fin (P + C * (P - 1)) → ℝ

/-- Number of variables minus number of constraints, computed in `ℤ`. -/

theorem phases_le (C P : ℕ) (hP : 1 ≤ P) (L : StateVars C P →ₗ[ℝ] Constraints C P)
    (hL : Function.Surjective L) : P ≤ C + 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hL] at h
  simp only [finrank_top, Module.finrank_fin_fun] at h
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hP
  simp only [Nat.add_sub_cancel_left] at h
  nlinarith [h, Nat.zero_le (Module.finrank ℝ (LinearMap.ker L))]

/-- **Gibbs phase rule.**  For a system of `C` components in `P ≥ 1` phases the intensive state
is described by `2 + P * C` variables (temperature, pressure and the mole fractions in every
phase), subject to `P + C * (P - 1)` independent equilibrium constraints (normalization of the
mole fractions in each phase and equality of the chemical potentials across the phases).
If the constraint map `L` is linear and independent (surjective), the space of admissible
variations — the direction space of the affine set of equilibrium states — has dimension

`F = C - P + 2`. -/
