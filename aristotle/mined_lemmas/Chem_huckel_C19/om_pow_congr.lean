/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma om_pow_congr {a b : ℕ} (h : a % 19 = b % 19) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 19]
  conv_rhs => rw [← Nat.div_add_mod b 19]
  simp [pow_add, pow_mul, om_pow_19, h]

