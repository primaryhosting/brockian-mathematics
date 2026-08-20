/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

open scoped Classical in
/-- The number of elements of `A` below `n`. -/

theorem hasAP_of_pos_upperDensity_of_le_three (A : Set ℕ) (hA : 0 < upperDensity A)
    {k : ℕ} (hk : k ≤ 3) : HasAP A k :=
  (hasAP_three_of_pos_upperDensity A hA).mono_length hk

/-! ### Further unconditional results -/

/-- Unconditional finitary Roth: the finitary Szemerédi property `SzemerediFinitary` holds
for `k = 3`, as a consequence of Mathlib's Roth theorem. -/
