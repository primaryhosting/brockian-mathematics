/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma zeta8_pow_mod (m : ℕ) : zeta8 ^ (m % 8) = zeta8 ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 8]
  rw [pow_add, pow_mul, zeta8_pow_eight, one_pow, one_mul]

/-- The additive character `x ↦ ζ₈ˣ` on `ZMod 8`. -/
