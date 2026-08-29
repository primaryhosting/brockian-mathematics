/-!
# Box Level 6
Category: Quantum Physics
Target: QPhys.box_level_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires every `import` command to precede any other
syntax in a file, so the mandated module docstring above forces this file to be
import-free (only the implicit `Init` prelude is available).  The statement below
is therefore phrased with the natural-number energy scale `e1` standing for the
ground-state energy `π²ħ²/(2mL²)` of the one-dimensional infinite square well.
The companion file `RequestProject/QPhysReal.lean` develops the same result for
the genuine real-valued formula `Eₙ = n²π²ħ²/(2mL²)` using Mathlib.
-/

namespace QPhys

/-- Energy levels of a particle in a one-dimensional infinite square well
("particle in a box"), expressed in units of the ground-state energy
`e1 = π²ħ²/(2mL²)`: the `n`-th level is `Eₙ = n² · e1`. -/

theorem boxEnergy_six (e1 : Nat) : boxEnergy e1 6 = 6 ^ 2 * boxEnergy e1 1 := by
  unfold boxEnergy
  simp

/-- The infinite-well energy ratio: `E₆ / E₁ = 6²`. -/
