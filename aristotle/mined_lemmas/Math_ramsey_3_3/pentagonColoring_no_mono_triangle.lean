/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Math


theorem pentagonColoring_no_mono_triangle :
    ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d →
      ¬(pentagonColoring s(a, b) = pentagonColoring s(a, d) ∧
        pentagonColoring s(a, d) = pentagonColoring s(b, d)) := by
  decide

/-- **R(3,3) = 6.**  Every 2-colouring of the edges of the complete graph `K₆`
contains a monochromatic triangle, while there is a 2-colouring of the edges of
`K₅` with no monochromatic triangle.  Edges are modelled as unordered pairs
`Sym2 (Fin n)`, and colours as `Bool`. -/
