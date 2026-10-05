/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-!
This file must literally begin with the header comment above, which Lean parses as a
module docstring; module docstrings have to precede every `import` command, so this
module is written using only Lean's core library (no `Mathlib` import) and works over
the rationals `Rat`.  The companion file `RequestProject/BoxLevel5Real.lean` states and
proves the same result over the real numbers `ℝ`, with `Real.pi` for `π`.
-/

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`
and circle constant `pi`:  `E n = n² π² ħ² / (2 m L²)`. -/

noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- **Box, level 5, over `ℝ`.**  For a particle in a one-dimensional infinite potential
well with nonzero mass, width and `hbar`, the ratio of the fifth energy level to the
ground state is `5² = 25`. -/
