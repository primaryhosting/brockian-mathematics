import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/

lemma C10_mul_dftMat : C10 * dftMat = dftMat * Matrix.diagonal huckelEigenvalue := by
  ext j k
  have hnb : (SimpleGraph.cycleGraph 10).neighborFinset j = {j - 1, j + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 8)
  have hne : ∀ j : ZMod 10, j - 1 ≠ j + 1 := by decide
  have hleft : (C10 * dftMat) j k = dftMat (j - 1) k + dftMat (j + 1) k := by
    rw [Matrix.mul_apply]
    have : (∑ l, C10 j l * dftMat l k)
        = (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 10)).mulVec
            (fun l => dftMat l k) j := rfl
    rw [this, SimpleGraph.adjMatrix_mulVec_apply, hnb]
    exact Finset.sum_pair (hne j)
  rw [hleft, Matrix.mul_diagonal]
  simp only [dftMat, Matrix.of_apply]
  rw [show (j - 1) * k = j * k + -k by ring, show (j + 1) * k = j * k + k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add, add_comm (chi (-k)) (chi k),
    chi_add_chi_neg]

