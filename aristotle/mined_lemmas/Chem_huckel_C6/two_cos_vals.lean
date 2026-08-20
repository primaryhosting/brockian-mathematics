/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₆` (the Hückel π-system of benzene) are
`2 cos (2πk/6)` for `k = 0, …, 5`.  This is stated as the factorization of the characteristic
polynomial of the adjacency matrix, so that eigenvalues are counted with multiplicity.

The proof diagonalizes the adjacency matrix explicitly: `A = P D P⁻¹` with `P` the (real)
matrix of eigenvectors and `D = diag(2, 1, 1, -1, -1, -2)`, then uses the Mathlib lemmas
`Matrix.charpoly_units_conj` and `Matrix.charpoly_diagonal`.
-/

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

lemma two_cos_vals (k : Fin 6) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = ![(2:ℝ), 1, -1, -2, -1, 1] k := by
  have hpi3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  fin_cases k <;> norm_num
  · rw [show (2:ℝ) * Real.pi / 6 = Real.pi / 3 by ring, hpi3]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 2 / 6 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, hpi3]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 3 / 6 = Real.pi by ring, Real.cos_pi]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 4 / 6 = 2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, hpi3]
    norm_num
  · rw [show (2:ℝ) * Real.pi * 5 / 6 = 2 * Real.pi - Real.pi / 3 by ring,
      Real.cos_two_pi_sub, hpi3]
    norm_num

/-- **Hückel theory for benzene (C₆).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₆` factors as
`∏_{k=0}^{5} (X - 2 cos (2πk/6))`; equivalently, the adjacency eigenvalues of `C₆`, counted
with multiplicity, are exactly `2 cos (2πk/6)` for `k = 0, …, 5`. -/
