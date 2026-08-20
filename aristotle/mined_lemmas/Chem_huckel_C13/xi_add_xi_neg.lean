/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix SimpleGraph

namespace Chem

/-- The primitive 13-th root of unity `exp (2πi/13)`. -/

lemma xi_add_xi_neg (j : Fin 13) :
    xi j + xi (-j) = 2 * Real.cos (2 * Real.pi * (j : ℕ) / 13) := by
  rw [xi_neg, xi_eq_exp, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.ofReal_cos]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Orthogonality of the characters: the character sum is `13` for the trivial character
and `0` otherwise. -/
