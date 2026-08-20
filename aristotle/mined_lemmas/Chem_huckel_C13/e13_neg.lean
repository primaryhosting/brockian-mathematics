import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma e13_neg (a : ZMod 13) : e13 (-a) = (e13 a)⁻¹ := by
  have h : e13 a * e13 (-a) = 1 := by rw [← e13_add]; simp
  exact (inv_eq_of_mul_eq_one_right h).symm

