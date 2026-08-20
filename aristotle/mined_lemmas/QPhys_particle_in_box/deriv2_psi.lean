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

lemma deriv2_psi (L : ℝ) (n : ℕ) :
    deriv (deriv (psi L n)) = fun x => -(((n : ℝ) * π / L) ^ 2) * psi L n x := by
  funext x; exact (hasDerivAt_deriv_psi L n x).deriv

/-- Antiderivative computation: `∫ sin (k x)² dx = x/2 - sin (2 k x)/(4 k)`. -/
