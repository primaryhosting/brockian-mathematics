/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/

lemma om_pow_congr {m n : ℕ} (h : m % 17 = n % 17) : om ^ m = om ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 17]
  conv_rhs => rw [← Nat.div_add_mod n 17]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_17, one_pow, one_pow, h]

/-- The additive character `k ↦ ω^k` on `ZMod 17`. -/
