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

lemma zeta19_pow_mod (m : ℕ) : zeta19 ^ (m % 19) = zeta19 ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, zeta19_pow19, one_pow, one_mul]

/-- The character `k ↦ ζ^k` on `Fin 19`. -/
