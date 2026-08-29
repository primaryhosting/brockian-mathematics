/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The finite square-lattice Ising model on an `L × L` torus -/

/-- The cyclic shift `i ↦ i + 1` on `Fin L` (periodic boundary conditions). -/

def shift {L : ℕ} (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- A spin configuration on the `L × L` torus: a `Bool` at each site. -/
abbrev Config (L : ℕ) := Fin L × Fin L → Bool

/-- `true ↦ +1`, `false ↦ -1`. -/
