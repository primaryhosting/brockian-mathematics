/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma w14_pow_congr {a b : ℕ} (h : a % 14 = b % 14) : w14 ^ a = w14 ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 14]
  conv_rhs => rw [← Nat.div_add_mod b 14]
  simp [pow_add, pow_mul, w14_pow_14, h]

