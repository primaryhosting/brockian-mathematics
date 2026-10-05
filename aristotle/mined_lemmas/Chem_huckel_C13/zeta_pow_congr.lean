/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/

lemma zeta_pow_congr {a b : ℕ} (h : a ≡ b [MOD 13]) : zeta ^ a = zeta ^ b := by
  have key : ∀ c : ℕ, zeta ^ c = zeta ^ (c % 13) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c 13]
    rw [pow_add, pow_mul, zeta_pow_thirteen, one_pow, one_mul]
  rw [key a, key b, h]

/-- `ζ^k + ζ^{-k} = 2 cos (2πk/13)`. -/
