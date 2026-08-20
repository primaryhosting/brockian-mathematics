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

lemma hasDerivAt_arg (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (n : ℝ) * π * x / L) ((n : ℝ) * π / L) x := by
  simpa [mul_div_assoc] using (((hasDerivAt_id x).const_mul ((n : ℝ) * π)).div_const L)

