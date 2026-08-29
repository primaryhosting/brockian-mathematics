/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma F18_isUnit : IsUnit F18 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, F18, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
  rw [sub_ne_zero]
  intro h
  exact absurd (zeta18_primitive.pow_inj j.isLt i.isLt h)
    (Fin.val_ne_of_ne (ne_of_gt (Finset.mem_Ioi.mp hj)))

/-- The eigenvalue equation `A · F = F · D`. -/
