/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

theorem C5adj_mulVec_eigenvector (k : ZMod 5) :
    C5adj.mulVec (huckelEigenvector k) = huckelEigenvalue k • huckelEigenvector k := by
  funext i
  have h := congrFun (congrFun C5adj_mul_F5 i) k
  simp only [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct, huckelEigenvector, Pi.smul_apply, smul_eq_mul]
  calc ∑ j, C5adj i j * e5 (j * k) = ∑ j, F5 i j * (Matrix.diagonal huckelEigenvalue) j k := h
    _ = huckelEigenvalue k * e5 (i * k) := by
        rw [Finset.sum_eq_single k (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb])
          (by simp)]
        simp [F5, mul_comm]

