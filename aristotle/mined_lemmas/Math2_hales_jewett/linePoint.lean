/-
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- The point of the combinatorial line determined by a nonempty set of "wildcard" coordinates
`S ⊆ Fin N` and a base point `b : Fin N → Fin k`, at parameter `x : Fin k`: the coordinates in
`S` all take the value `x`, and the remaining coordinates keep the value given by `b`. -/

def linePoint {N k : ℕ} (S : Finset (Fin N)) (b : Fin N → Fin k) (x : Fin k) : Fin N → Fin k :=
  fun i => if i ∈ S then x else b i

/-- A combinatorial line, given by wildcard set `S` and base point `b`, is monochromatic for the
coloring `C` if all of its `k` points get the same color. -/
