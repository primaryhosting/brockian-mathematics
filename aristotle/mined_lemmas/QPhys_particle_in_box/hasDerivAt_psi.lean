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

lemma hasDerivAt_psi (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (psi L n)
      (Real.sqrt (2 / L) * (((n : ℝ) * π / L) * Real.cos (n * π * x / L))) x := by
  have h2 := ((hasDerivAt_arg L n x).sin).const_mul (Real.sqrt (2 / L))
  convert h2 using 1
  ring

