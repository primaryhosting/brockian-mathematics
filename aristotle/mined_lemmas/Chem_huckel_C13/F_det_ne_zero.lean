import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
(The `import Mathlib` line must precede the module docstring: Lean 4 requires all
`import` commands to appear at the very beginning of a file.)
-/

namespace Chem

open Matrix SimpleGraph Finset

/-- A primitive 13-th root of unity. -/

lemma F_det_ne_zero : F.det ≠ 0 := by
  rw [F, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have : ev j ≠ ev i := by
    intro h
    have := zt_isPrimitiveRoot.pow_inj j.isLt i.isLt h
    exact absurd (Fin.ext this) (ne_of_gt hij)
  exact sub_ne_zero_of_ne this

/-- The adjacency matrix of the cycle graph `C₁₃`. -/
