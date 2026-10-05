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

private theorem rat_mul_div_cancel (a x : Rat) (hx : x ≠ 0) : a * x / x = a := by
  rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel x hx, Rat.mul_one]

/-- **Box, level 5.**  For a particle in a one-dimensional infinite potential well with
nonvanishing ground-state energy, the ratio of the fifth energy level to the ground state
is `5² = 25`. -/
