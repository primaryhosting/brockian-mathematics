/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! -/` module docstring,
-- because in Lean 4.28 a module docstring is a command and cannot precede `import`.
-- The same text is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel spectrum of the cyclic polyene C₁₉: the eigenvalues of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)`, `k = 0, …, 18`.

The proof identifies the adjacency matrix with `S + S¹⁸`, where `S` is the cyclic shift matrix
(a circulant matrix), computes `spectrum ℂ S` (all 19-th roots of unity), and then applies the
spectral mapping theorem `spectrum.map_polynomial_aeval_of_degree_pos` for the polynomial
`X + X ^ 18`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Matrix Complex Polynomial SimpleGraph

/-- A primitive 19-th root of unity. -/

lemma cycleGraph19_adj (i j : Fin 19) :
    (SimpleGraph.cycleGraph 19).Adj i j ↔ (i - j = 1 ∨ i - j = 18) := by
  rw [SimpleGraph.cycleGraph_adj (n := 17)]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have hh : i - j = -(j - i) := by abel
      rw [hh, h]; decide
  · rintro (h | h)
    · exact Or.inl h
    · right
      have hh : j - i = -(i - j) := by abel
      rw [hh, h]; decide

/-- The adjacency matrix of `C₁₉` is `S + S¹⁸`, where `S` is the cyclic shift. -/
