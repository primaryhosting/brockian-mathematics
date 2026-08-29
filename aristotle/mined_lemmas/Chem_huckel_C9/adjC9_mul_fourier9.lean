/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

theorem adjC9_mul_fourier9 : adjC9 * fourier9 = fourier9 * diagC9 := by
  ext j k
  rw [Matrix.mul_apply, diagC9, Matrix.mul_diagonal]
  have hsum : ∑ l : ZMod 9, adjC9 j l * ff (l * k) = ff ((j - 1) * k) + ff ((j + 1) * k) := by
    simp only [adjC9_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h1 : (j - 1) * k = j * k + -k := by ring
  have h2 : (j + 1) * k = j * k + k := by ring
  simp only [fourier9, Matrix.of_apply]
  rw [hsum, h1, h2, ff_add, ff_add]
  ring

