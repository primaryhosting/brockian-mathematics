/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires every `import` command to appear before any other
syntax in a file, so this file — whose first token must be the header comment
above — is written without imports.  It therefore uses only the Lean core
library, in particular the core field class `Lean.Grind.Field`, which the real
numbers of Mathlib instantiate.  The Mathlib specialisation to `ℝ` with the
genuine constant `Real.pi` is in `RequestProject/BoxLevel7Real.lean`.
-/

namespace QPhys

open Lean.Grind

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant
`hbar` and circle constant `pi`:

`E n = n² π² ħ² / (2 m L²)`.

The level index `n` is taken in the ambient field `K`; the physical levels are
the values at `n = 1, 2, 3, …`. -/

theorem boxEnergyReal_eq (hbar m L : ℝ) (n : ℕ) :
    boxEnergyReal hbar m L n = (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2) :=
  rfl

/-- **Box level 7 over `ℝ`.**  For a particle of nonzero mass `m` in a
one-dimensional infinite well of nonzero width `L`, with nonzero reduced Planck
constant `ħ`, the ratio of the seventh energy level to the ground state energy
is `7² = 49`. -/
