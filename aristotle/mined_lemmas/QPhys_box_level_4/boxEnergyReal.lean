/-!
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the shape of this file: Lean 4 requires every `import` command to come before any
other command, including a module docstring.  Since the header comment above must literally
be the first thing in the file, this file cannot import Mathlib, and is therefore developed
in plain Lean 4 core over the rationals, with the energy scale `c = π²ℏ²/(2mL²)` of the well
kept as a parameter.  The fully explicit real-valued companion statement (with `π`, `ℏ`, the
mass `m` and the width `L` spelled out over `ℝ`) is proved as `QPhys.box_level_4_real` in
`RequestProject/BoxLevel4Real.lean`.
-/

namespace QPhys

/-- Energy levels of a particle in a one-dimensional infinite square well
("particle in a box"):  `Eₙ = n² · c`, where `c = π²ℏ²/(2mL²)` is the energy scale of the
well (so `c = E₁` is the ground-state energy). -/

noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- **Infinite-well energy ratio, real-valued form.**  `E₄ / E₁ = 4² = 16`. -/
