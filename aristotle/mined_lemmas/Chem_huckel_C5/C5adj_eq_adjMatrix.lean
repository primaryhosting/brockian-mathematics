/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the 5-cycle `C₅`

The Hückel secular problem for the cyclic polyene `C₅H₅` reduces (after removing the
Coulomb integral `α` and dividing by the resonance integral `β`) to the eigenvalue
problem for the adjacency matrix of the cycle graph `C₅`.

The main result `Chem.huckel_C5` states that the eigenvalues of that adjacency matrix
are exactly the five numbers `2 * cos (2 * π * k / 5)`, `k = 0, 1, 2, 3, 4`
(equivalently `2`, `(√5 - 1)/2` twice and `-(√5 + 1)/2` twice).
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where `α = 0`, `β = 1`). -/

theorem C5adj_eq_adjMatrix : C5adj = (SimpleGraph.cycleGraph 5).adjMatrix ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C5adj, SimpleGraph.adjMatrix, SimpleGraph.cycleGraph_adj] <;> decide

section Auxiliary

/-- For a fifth root of unity `z`, the vector `(1, z, z², z³, z⁴)` is an eigenvector of
the `C₅` adjacency matrix with eigenvalue `z + z⁴ = z + z⁻¹`. -/
