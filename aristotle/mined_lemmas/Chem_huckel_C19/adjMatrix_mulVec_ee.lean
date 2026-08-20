/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem adjMatrix_mulVec_ee (k : Fin 19) :
    AC19 *ᵥ (fun i => ee (i * k)) = mu k • (fun i => ee (i * k)) := by
  funext i
  have hnbr : (SimpleGraph.cycleGraph 19).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 17)
  have e1 : ee ((i + 1) * k) = ee (i * k) * ee k := by
    rw [← ee_add, add_mul, one_mul]
  have e2 : ee ((i - 1) * k) = ee (i * k) * ee (-k) := by
    rw [← ee_add, sub_mul, one_mul, sub_eq_add_neg]
  rw [AC19, SimpleGraph.adjMatrix_mulVec_apply, hnbr,
    Finset.sum_pair (sub_one_ne_add_one i), e1, e2, Pi.smul_apply, smul_eq_mul, ← ee_add_neg]
  ring

/-- The inverse (up to normalization) of the Fourier matrix. -/
