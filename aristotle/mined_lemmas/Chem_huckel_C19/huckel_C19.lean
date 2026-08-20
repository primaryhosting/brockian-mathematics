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

theorem huckel_C19 :
    spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ) =
      Set.range (fun k : Fin 19 => ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)) := by
  have hp : (Polynomial.aeval shift19) (X + X ^ 18 : ℂ[X]) =
      (SimpleGraph.cycleGraph 19).adjMatrix ℂ := by
    rw [adjMatrix_cycleGraph19]
    simp
  have hd : (X + X ^ 18 : ℂ[X]).degree = 18 := by compute_degree!
  have hdeg : 0 < (X + X ^ 18 : ℂ[X]).degree := by
    rw [hd]; decide
  rw [← hp, spectrum.map_polynomial_aeval_of_degree_pos _ _ hdeg, spectrum_shift19,
    ← Set.range_comp]
  apply congrArg
  funext k
  simpa using eval_eigenvalue (k : ℕ)

end Chem

