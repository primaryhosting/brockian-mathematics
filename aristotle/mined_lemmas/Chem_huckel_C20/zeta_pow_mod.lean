import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 20) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 20]
  rw [pow_add, pow_mul, zeta_pow_twenty, one_pow, one_mul]

/-- The character `k ↦ ζ^k` on `Fin 20` (viewed as `ZMod 20`). -/
