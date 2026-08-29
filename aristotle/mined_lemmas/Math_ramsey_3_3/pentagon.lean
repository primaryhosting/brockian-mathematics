/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- An auxiliary "vector" of five booleans, read off as a function on `Fin 6` (the value at
the index `0` is irrelevant and set to `false`). -/

private def pentagon (i j : Fin 5) : Bool :=
  decide ((i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)

/-- **R(3,3) = 6.**

A 2-colouring of the edges of a complete graph is modelled as a symmetric `Bool`-valued
function on pairs of vertices, and a monochromatic triangle is a triple of pairwise distinct
vertices all three of whose connecting edges receive the same colour.

The first conjunct states that every 2-colouring of the edges of `K₆` contains a
monochromatic triangle (note that the symmetry hypothesis, which is part of the notion of an
edge colouring, turns out not to be needed for this direction). The second conjunct exhibits
a 2-colouring of the edges of `K₅` — the pentagon colouring — with no monochromatic
triangle. -/
