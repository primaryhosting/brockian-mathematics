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

lemma zeta8_pow_eight : zeta8 ^ 8 = 1 := by
  rw [zeta8, ← Complex.exp_nat_mul]
  have h : (8 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 8) = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.exp_two_pi_mul_I

