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

lemma adjMatrix_cycleGraph19 :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ = shift19 + shift19 ^ 18 := by
  rw [shift19_pow_18, shift19, ← Matrix.circulant_add]
  ext i j
  rw [SimpleGraph.adjMatrix_apply, Matrix.circulant_apply]
  simp only [cycleGraph19_adj, Pi.add_apply, Pi.single_apply]
  by_cases h1 : i - j = 1 <;> by_cases h2 : i - j = 18 <;> simp [h1, h2]

/-- If `M *ᵥ v = μ • v` for a nonzero vector `v`, then `μ` lies in the spectrum of `M`. -/
