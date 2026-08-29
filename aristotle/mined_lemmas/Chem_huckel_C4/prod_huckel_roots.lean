/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Polynomial Real

/-- Adjacency matrix of the cycle graph `C n` on the vertex set `Fin n`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `n`. -/

lemma prod_huckel_roots :
    (∏ k : Fin 4, (X - C (2 * Real.cos (2 * π * (k : ℕ) / 4)))) = X ^ 4 - 4 * X ^ 2 := by
  have h1 : (2 * π * (1 : ℕ) / 4 : ℝ) = π / 2 := by push_cast; ring
  have h2 : (2 * π * (2 : ℕ) / 4 : ℝ) = π := by push_cast; ring
  have h3 : (2 * π * (3 : ℕ) / 4 : ℝ) = π + π / 2 := by push_cast; ring
  rw [Fin.prod_univ_four]
  norm_num [h1, h2, h3, Real.cos_add]
  ring

/-- **Hückel theory for cyclobutadiene (C₄).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C 4`
factors as `∏ k, (X - 2 cos (2πk/4))`; equivalently, the adjacency eigenvalues of
`C 4` are exactly `2 cos (2πk/4)` for `k = 0, 1, 2, 3` (counted with multiplicity). -/
