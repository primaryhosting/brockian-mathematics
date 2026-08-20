/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Statement: Any finite coloring of ℕ has arbitrarily long monochromatic APs (van der Waerden).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- `HasAP c m N` says the coloring `c` admits a monochromatic arithmetic progression of
length `m` with positive common difference, contained (together with a little slack) in
`[0, N]`. -/

@[reducible] def HasAP {K : Type*} (c : ℕ → K) (m N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + m * d ≤ N ∧ ∀ i < m, c (a + i * d) = c a

/-- `FanFamily c k s N` says there are `s` monochromatic arithmetic progressions of length `k`,
pairwise of different colors, all "focused" at a common point `f ≤ N`. -/
