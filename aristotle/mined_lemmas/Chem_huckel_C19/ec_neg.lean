import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/

lemma ec_neg (a : Fin 19) : ec (-a) = (ec a)⁻¹ := by
  have h : ec a * ec (-a) = 1 := by rw [← ec_add, add_neg_cancel, ec_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

