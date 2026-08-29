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

lemma sum_const_config (L : ℕ) (c : ℝ) :
    ∑ _σ : Config L, c = 2 ^ (L * L) * c := by
  rw [Finset.sum_const, Finset.card_univ, card_config, nsmul_eq_mul]
  push_cast
  ring

/-- At infinite temperature (`K = 0`) every configuration has weight one. -/
