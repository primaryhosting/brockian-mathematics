import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- The adjacency matrix of the cycle graph `C₁₃` (the Hückel matrix of the
`C₁₃` carbon ring, in units where `α = 0` and `β = 1`). -/

lemma pow_mod13 {z : ℂ} (hz : z ^ 13 = 1) (x : ℕ) : z ^ (x % 13) = z ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 13]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

