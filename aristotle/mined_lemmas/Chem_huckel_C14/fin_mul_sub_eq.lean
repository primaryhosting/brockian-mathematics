/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma fin_mul_sub_eq (k x y : Fin 14) : k * x + -(k * y) = k * (x - y) := by
  rw [mul_sub, sub_eq_add_neg]

/-! ### Character orthogonality and Fourier inversion -/

/-- Orthogonality of characters: the character sum vanishes unless `d = 0`. -/
