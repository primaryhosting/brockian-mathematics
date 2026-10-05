/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Pigeonhole on five vertices two-coloured: three of them get the same colour. -/

def cycleColoring : Fin 5 → Fin 5 → Bool := fun i j => decide (i - j = 1 ∨ i - j = 4)

/-- **R(3,3) = 6**: every 2-colouring of the edges of `K₆` contains a monochromatic
triangle, while `K₅` admits a 2-colouring with no monochromatic triangle. -/
