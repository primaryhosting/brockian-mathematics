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

private lemma C5adj_mulVec_pow (z : ℂ) (h5 : z ^ 5 = 1) :
    C5adj.mulVec ![1, z, z ^ 2, z ^ 3, z ^ 4] = (z + z ^ 4) • ![1, z, z ^ 2, z ^ 3, z ^ 4] := by
  have h6 : z ^ 6 = z := by linear_combination z * h5
  have h7 : z ^ 7 = z ^ 2 := by linear_combination z ^ 2 * h5
  have h8 : z ^ 8 = z ^ 3 := by linear_combination z ^ 3 * h5
  funext i
  fin_cases i <;>
    simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;>
    ring_nf <;> simp only [h5, h6, h7, h8] <;> ring

/-- `exp (2πik/5)` is a fifth root of unity. -/
