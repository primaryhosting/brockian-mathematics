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

noncomputable def onsagerKc : ℝ := Real.log (1 + Real.sqrt 2) / 2

section Lemmas

/-- `sinh (2 K_c) = 1`: the Kramers–Wannier self-duality condition at the critical point. -/
