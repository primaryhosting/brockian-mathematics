/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Real

namespace Frontier

/-- A Boolean spin variable read as a real number `±1`. -/

noncomputable def isingEnergy (n : ℕ) (σ : ZMod (n + 1) × ZMod (n + 1) → Bool) : ℝ :=
  ∑ x : ZMod (n + 1) × ZMod (n + 1),
    (spin (σ x) * spin (σ (x.1 + 1, x.2)) + spin (σ x) * spin (σ (x.1, x.2 + 1)))

/-- The partition function of the 2D Ising model on the `(n+1) × (n+1)` periodic square lattice
at reduced coupling `K = βJ`. -/
