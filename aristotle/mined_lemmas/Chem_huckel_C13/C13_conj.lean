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

lemma C13_conj : C13 = (Uunit : Matrix (Fin 13) (Fin 13) ℂ) * Matrix.diagonal eval13 *
    ((Uunit⁻¹ : (Matrix (Fin 13) (Fin 13) ℂ)ˣ) : Matrix (Fin 13) (Fin 13) ℂ) :=
  calc C13 = C13 * (U * V) := by rw [U_mul_V, mul_one]
    _ = C13 * U * V := by rw [mul_assoc]
    _ = U * Matrix.diagonal eval13 * V := by rw [C13_mul_U]

/-- The characteristic polynomial of the Hückel matrix of `C₁₃` factors as
`∏ k, (X - 2 cos (2πk/13))`, so the thirteen eigenvalues (with multiplicity) are exactly
`2 cos (2πk/13)` for `k = 0, 1, …, 12`. -/
