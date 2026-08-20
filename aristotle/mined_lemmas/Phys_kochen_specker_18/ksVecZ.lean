/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
with integer entries. -/

def ksVecZ : Fin 18 → Fin 4 → ℤ :=
  ![![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![1, 1, 0, 0],
    ![1, -1, 0, 0],
    ![0, 1, 0, 0],
    ![1, 0, 1, 0],
    ![1, 0, -1, 0],
    ![1, -1, 1, -1],
    ![1, -1, -1, 1],
    ![0, 0, 1, 1],
    ![1, 1, 1, 1],
    ![0, 1, 0, -1],
    ![1, 0, 0, 1],
    ![1, 0, 0, -1],
    ![0, 1, -1, 0],
    ![1, 1, -1, 1],
    ![1, 1, 1, -1],
    ![-1, 1, 1, 1]]

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
as vectors in `ℝ⁴`. -/
