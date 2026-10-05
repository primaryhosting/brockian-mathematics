import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma zeta_pow_mod (a : ℕ) : zeta ^ (a % 13) = zeta ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 13]
  rw [pow_add, pow_mul, zeta_pow13, one_pow, one_mul]

/-- The additive character `x ↦ ζ ^ x` of `ZMod 13`. -/
