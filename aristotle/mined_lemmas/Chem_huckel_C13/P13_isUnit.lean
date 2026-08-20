import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma P13_isUnit : IsUnit P13 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, P13, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  exact sub_ne_zero_of_ne fun h => absurd (qc_injective h) hj.ne'

