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

@[simp] theorem boxEnergy_def (E1 : Rat) (n : Nat) :
    boxEnergy E1 n = (n : Rat) ^ 2 * E1 := rfl

/-- The ground state indeed has energy `E₁`. -/
