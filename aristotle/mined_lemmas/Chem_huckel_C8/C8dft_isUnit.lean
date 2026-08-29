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

lemma C8dft_isUnit : IsUnit C8dft := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, C8dft]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b h
  exact Fin.ext (zeta8_prim.pow_inj a.isLt b.isLt h)

/-- `C8adj` is indeed the adjacency matrix of Mathlib's cycle graph on `8` vertices. -/
