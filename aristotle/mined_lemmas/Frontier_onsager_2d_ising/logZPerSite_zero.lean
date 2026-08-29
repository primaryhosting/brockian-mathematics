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

lemma logZPerSite_zero (L : ℕ) (hL : 0 < L) : logZPerSite L 0 = onsagerLogZ 0 := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  rw [logZPerSite, isingZ_zero, onsagerLogZ_zero, Real.log_pow]
  push_cast
  field_simp

/-- **Lean-checked reduction: uniform continuity at infinite temperature.**
For every `L` and every `K`, the finite-volume free energy differs from the Onsager
value at `K = 0` by at most `2|K|`, uniformly in the volume. -/
