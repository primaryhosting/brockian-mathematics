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

lemma C13_mul_U : C13 * U = U * Matrix.diagonal eval13 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have h : ∑ l, C13 j l * U l k = (C13 *ᵥ vec k) j := rfl
  rw [h, C13_mulVec_vec, Pi.smul_apply, smul_eq_mul, U, mul_comm]

/-- **Hückel theory for the `C₁₃` ring.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₃` if and only if it is of the form
`2 * cos (2 * π * k / 13)` for some `k = 0, 1, …, 12`. -/
