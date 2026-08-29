import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem chi_natCast (m : ℕ) : chi ((m : ZMod 10)) = om ^ m := by
  rw [chi, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod m 10]
  rw [pow_add, pow_mul, om_pow_ten, one_pow, one_mul]

