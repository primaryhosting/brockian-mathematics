import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

lemma det_V12_ne_zero : (V12).det ≠ 0 := by
  rw [V12, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro hzero
  have heq := om_prim.pow_inj j.isLt i.isLt hzero
  have hlt : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
  omega

