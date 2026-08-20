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

theorem C10_spectrum :
    spectrum ℂ C10 = {z : ℂ | ∃ k : ZMod 10, z = huckelEigenvalue k} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, C10_charpoly]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero,
    Set.mem_setOf_eq]

/-- **Hückel theory for `C₁₀`.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₀` is `∏ k, (X - 2 cos (2πk/10))`; consequently its spectrum (the set of
eigenvalues) is exactly `{2 cos (2πk/10) : k = 0, …, 9}`. -/
