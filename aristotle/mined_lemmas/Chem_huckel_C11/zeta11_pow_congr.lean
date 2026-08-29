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

lemma zeta11_pow_congr {a b : ℕ} (h : a % 11 = b % 11) : zeta11 ^ a = zeta11 ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 11]
  conv_rhs => rw [← Nat.div_add_mod b 11]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta11_pow_eleven, one_pow, one_pow, h]

/-- The additive character `x ↦ ζ^x` on `Fin 11`. -/
