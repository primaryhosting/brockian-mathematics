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

def IsMonoLine {N k r : ℕ} (C : (Fin N → Fin k) → Fin r) (S : Finset (Fin N))
    (b : Fin N → Fin k) : Prop :=
  ∃ c : Fin r, ∀ x : Fin k, C (linePoint S b x) = c

/-- **The Hales–Jewett theorem.** For every alphabet size `k > 0` and every number of colors `r`,
there is a dimension `N > 0` such that every `r`-coloring of the combinatorial hypercube
`[k]^N = (Fin N → Fin k)` admits a monochromatic combinatorial line: a nonempty set `S` of
wildcard coordinates and a base point `b` off `S` such that the `k` points
`fun i => if i ∈ S then x else b i`, for `x : Fin k`, all receive the same color. -/
