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

lemma ec_natCast_mul (m : ℕ) (d : Fin 19) : ec ((m : Fin 19) * d) = ec d ^ m := by
  induction m with
  | zero => simp [ec_zero]
  | succ m ih =>
      have : ((m + 1 : ℕ) : Fin 19) * d = (m : Fin 19) * d + d := by push_cast; ring
      rw [this, ec_add, ih, pow_succ]

