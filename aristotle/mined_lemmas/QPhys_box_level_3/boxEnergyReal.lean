import Mathlib

/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Real-valued companion to `RequestProject/Main.lean`: the infinite square well
spectrum with the explicit physical constants `ħ`, `m`, `L` and `Real.pi`.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well of width `L`:
`E n = n² π² ħ² / (2 m L²)`. -/

noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The spectrum is `n²` times the ground-state energy. -/
