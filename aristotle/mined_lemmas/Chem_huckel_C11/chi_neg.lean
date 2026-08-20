/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset Complex

noncomputable section

/-- A primitive 11-th root of unity. -/

lemma chi_neg (x : ZMod 11) : chi (-x) = (chi x)⁻¹ := by
  have h : chi (-x) * chi x = 1 := by rw [← chi_add]; simp [chi_zero]
  exact eq_inv_of_mul_eq_one_left h

