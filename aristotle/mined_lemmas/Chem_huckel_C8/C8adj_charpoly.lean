import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma C8adj_charpoly :
    C8adj.charpoly = ∏ k : Fin 8, (X - C (2 * Real.cos (2 * Real.pi * k / 8) : ℂ)) := by
  obtain ⟨u, hu⟩ := C8dft_isUnit
  have hconj :
      C8adj = u.val * Matrix.diagonal C8eigen * (u⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ).val := by
    rw [Units.eq_mul_inv_iff_mul_eq, hu]
    exact C8adj_mul_dft
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

/-- **Hückel theory for cyclic C₈.** The characteristic polynomial of the adjacency
matrix of the cycle graph `C₈` factors completely with roots `2 cos (2πk/8)`,
`k = 0, …, 7`; that is, the adjacency eigenvalues of `C₈` are exactly
`2 cos (2πk/8)` for `k = 0, …, 7` (counted with multiplicity). -/
