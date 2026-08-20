import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma P_det_ne_zero : P.det ≠ 0 := by
  rw [P, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  simp only [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne ?_
  intro h
  exact absurd (Fin.ext (zeta_isPrimitiveRoot.pow_inj j.isLt i.isLt h)) hj.ne'

/-- Shifting the index by `+1` multiplies the power by `x`. -/
