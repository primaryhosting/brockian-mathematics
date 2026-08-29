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

theorem box_level_3_real (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 3 / boxEnergyReal hbar m L 1 = (3 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  push_cast
  field_simp

end QPhys

/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any
other command, including module doc comments.  Since this file must *begin* with
the header comment above, it is written in dependency-free core Lean 4.  The
companion file `RequestProject/Box.lean` develops the same physics with Mathlib,
using real numbers, `Real.pi`, and the explicit constants `ħ`, `m`, `L`.
-/

namespace QPhys

/-- Stationary-state energies of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`:

  `E n = n² · π²ħ²/(2mL²) = n² · E₁`,

where `E₁` is the ground-state energy.  Here the spectrum is parameterised by
the ground-state energy `E₁` (the overall energy scale), so that
`boxEnergy E₁ n` is the energy of the `n`-th level. -/
