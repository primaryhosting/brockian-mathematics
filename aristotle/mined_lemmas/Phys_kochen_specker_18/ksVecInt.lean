/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
given with integer coordinates. -/

def ksVecInt : Fin 18 → Fin 4 → ℤ :=
  ![ ![0, 0, 0, 1],    -- 0
     ![0, 0, 1, 0],    -- 1
     ![1, 1, 0, 0],    -- 2
     ![1, -1, 0, 0],   -- 3
     ![0, 1, 0, 0],    -- 4
     ![1, 0, 1, 0],    -- 5
     ![1, 0, -1, 0],   -- 6
     ![1, -1, 1, -1],  -- 7
     ![1, -1, -1, 1],  -- 8
     ![0, 0, 1, 1],    -- 9
     ![1, 1, 1, 1],    -- 10
     ![0, 1, 0, -1],   -- 11
     ![1, 0, 0, 1],    -- 12
     ![1, 0, 0, -1],   -- 13
     ![1, 1, -1, 1],   -- 14
     ![1, 1, 1, -1],   -- 15
     ![-1, 1, 1, 1],   -- 16
     ![0, 1, -1, 0] ]  -- 17

/-- The 18 vectors of the Kochen–Specker set, as real vectors in `ℝ⁴`. -/
