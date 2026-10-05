/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem zeta_pow_congr {m n : ℕ} (h : m % 7 = n % 7) : zeta ^ m = zeta ^ n := by
  have key : ∀ p : ℕ, zeta ^ p = zeta ^ (p % 7) := by
    intro p
    conv_lhs => rw [show p = 7 * (p / 7) + p % 7 from (Nat.div_add_mod p 7).symm]
    rw [pow_add, pow_mul, zeta_pow_seven, one_pow, one_mul]
  rw [key m, key n, h]

