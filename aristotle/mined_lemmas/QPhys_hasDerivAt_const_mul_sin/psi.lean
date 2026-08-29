/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The normalized stationary states of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

noncomputable def psi (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (2 / L) * Real.sin (n * Real.pi * x / L)

/-- The energy levels of the infinite square well of width `L`:
`E_n = n²π²ℏ²/(2mL²)`. -/
