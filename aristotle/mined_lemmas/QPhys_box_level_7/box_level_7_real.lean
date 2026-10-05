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

theorem box_level_7_real {hbar m L : ℝ} (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 7 / boxEnergyReal hbar m L 1 = 7 ^ 2 := by
  have h : boxEnergyReal hbar m L 7 / boxEnergyReal hbar m L 1
      = boxEnergy hbar m L Real.pi 7 / boxEnergy hbar m L Real.pi 1 := by
    unfold boxEnergyReal
    norm_num
  rw [h]
  exact box_level_7 hbar m L Real.pi (by norm_num) hhbar hm hL Real.pi_ne_zero

end QPhys

