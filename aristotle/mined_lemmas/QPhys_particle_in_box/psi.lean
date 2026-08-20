/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain comment and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Real

/-- The (unnormalized-constant times) `n`-th stationary state of the infinite square
well of width `L`: `ψ n x = c * sin (n π x / L)`. -/

noncomputable def psi (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (2 / L) * Real.sin (n * π * x / L)

/-- The `n`-th energy level of the infinite square well of width `L`,
for a particle of mass `m` with reduced Planck constant `hbar`. -/
