/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Complex Matrix

/-- The primitive 14-th root of unity `exp(2πi/14)`. -/

lemma dftMat_det_ne_zero : (dftMat).det ≠ 0 := by
  rw [dftMat, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  refine sub_ne_zero_of_ne fun h => ?_
  have := om_prim.pow_inj j.isLt i.isLt h
  exact absurd (Fin.ext this) (ne_of_gt hij)

/-- The adjacency matrix of `C₁₄` is conjugate (by the invertible Fourier matrix) to the
diagonal matrix of the Hückel eigenvalues. -/
