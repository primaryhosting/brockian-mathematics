/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

lemma zeta_pow_congr {a b : ℕ} (h : a % 10 = b % 10) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 10]
  conv_rhs => rw [← Nat.div_add_mod b 10]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta_pow_ten, one_pow, one_pow, h]

