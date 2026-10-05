/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma pow_mod_twenty {a : ℂ} (ha : a ^ 20 = 1) (n : ℕ) : a ^ (n % 20) = a ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 20, pow_add, pow_mul, ha, one_pow, one_mul]

/-- If `a ^ 20 = 1`, then `i ↦ a ^ i.val` is multiplicative on `ZMod 20`. -/
