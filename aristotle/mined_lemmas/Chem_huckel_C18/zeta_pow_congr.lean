/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem zeta_pow_congr {a b : ℕ} (h : a % 18 = b % 18) : zeta ^ a = zeta ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 18]
  conv_rhs => rw [← Nat.div_add_mod b 18]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta_pow_18, one_pow, one_pow, h]

