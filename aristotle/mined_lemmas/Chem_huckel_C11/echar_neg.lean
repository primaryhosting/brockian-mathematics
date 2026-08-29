/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

lemma echar_neg (x : Fin 11) : echar (-x) = (echar x)⁻¹ := by
  have h : echar (-x) * echar x = 1 := by rw [← echar_add]; simp [echar_zero]
  exact eq_inv_of_mul_eq_one_left h

/-- Orthogonality of characters: the sum over all `j` of `echar (j * c)`. -/
