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

theorem energy_levels_pos (hbar m L : ℝ) (hbar0 : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L)
    (n : ℕ) (hn : 1 ≤ n) : 0 < E hbar m L n := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have : (0:ℝ) < hbar ^ 2 := by positivity
  unfold E
  positivity

/-- The energy levels increase strictly with `n`. -/
