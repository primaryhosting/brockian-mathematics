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

lemma echar_mul (x y : Fin 11) : echar (x * y) = (echar y) ^ (x : ℕ) := by
  rw [echar, echar, ← pow_mul]
  exact zeta11_pow_congr (by simp [Fin.val_mul, Nat.mul_mod, mul_comm])

