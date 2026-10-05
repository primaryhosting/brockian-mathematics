/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/

theorem spectrum_diagonal_eq (d : ZMod 11 → ℂ) :
    spectrum ℂ (Matrix.diagonal d) = Set.range d := by
  ext z
  rw [spectrum.mem_iff]
  have halg : (algebraMap ℂ (Matrix (ZMod 11) (ZMod 11) ℂ)) z - Matrix.diagonal d
      = Matrix.diagonal (fun i => z - d i) := by
    rw [Matrix.algebraMap_eq_diagonal, ← Matrix.diagonal_sub]
    rfl
  rw [halg, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero,
    not_not, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, by rw [← hi]; ring⟩

/-- **Hückel theory for the C₁₁ cycle.**  The eigenvalues (spectrum) of the adjacency matrix
of the cycle graph `C₁₁` are exactly the numbers `2 cos (2πk/11)` for `k = 0, …, 10`. -/
