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

lemma zeta_pow_twelve_add (k : Fin 13) : zeta k ^ 12 + zeta k = eval13 k := by
  have hz0 : zeta k ≠ 0 := zeta_ne_zero k
  have h12 : zeta k ^ 12 = (zeta k)⁻¹ := by
    field_simp
    linear_combination zeta_pow13 k
  rw [eval13, h12, zeta_eq_exp, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul, add_comm]

