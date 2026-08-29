import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/

lemma pow_val_add {y : ℂ} (hy : y ^ 7 = 1) (a b : ZMod 7) :
    y ^ (a + b).val = y ^ a.val * y ^ b.val := by
  have hmod : ∀ m : ℕ, y ^ (m % 7) = y ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 7, pow_add, pow_mul, hy, one_pow, one_mul]
  rw [ZMod.val_add, hmod, pow_add]

/-- Iterating a shift relation `u (i + 1) = y * u i`. -/
