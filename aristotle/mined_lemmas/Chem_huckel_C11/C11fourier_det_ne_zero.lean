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

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

theorem C11fourier_det_ne_zero : C11fourier.det ≠ 0 := by
  rw [C11fourier, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  intro h
  have h1 : zeta11 ^ (j : ℕ) = zeta11 ^ (i : ℕ) := sub_eq_zero.mp h
  have h2 : (j : ℕ) = (i : ℕ) := isPrimitiveRoot_zeta11.pow_inj j.isLt i.isLt h1
  exact absurd (Fin.ext h2) (Fin.ne_of_gt hj)

/-- **Hückel theory for the cycle `C₁₁`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₁` is `∏_{k=0}^{10} (X - 2 cos (2πk/11))`, i.e. the adjacency
eigenvalues of `C₁₁` are exactly `2 cos (2πk/11)` for `k = 0, …, 10` (with multiplicity). -/
