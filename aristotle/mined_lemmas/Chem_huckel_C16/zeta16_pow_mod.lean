/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

lemma zeta16_pow_mod (a : ℕ) : zeta16 ^ a = zeta16 ^ (a % 16) := by
  conv_lhs => rw [← Nat.div_add_mod a 16]
  rw [pow_add, pow_mul, zeta16_pow_sixteen, one_pow, one_mul]

