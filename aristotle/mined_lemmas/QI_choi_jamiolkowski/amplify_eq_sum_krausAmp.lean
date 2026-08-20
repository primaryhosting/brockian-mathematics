/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C (i,a) (j,b) = (Φ Eᵢⱼ) a b`, where `Eᵢⱼ` is the matrix unit. -/

theorem amplify_eq_sum_krausAmp (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {r : ℕ}
    {K : Fin r → Matrix m n ℂ} (hK : ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ)
    (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix (κ × n) (κ × n) ℂ) :
    amplify Φ κ X = ∑ k, krausAmp κ (K k) * X * (krausAmp κ (K k))ᴴ := by
  ext x y
  simp only [amplify, Matrix.of_apply, hK, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_krausAmp_conjTranspose_apply]
  simp only [krausAmp_mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

omit [DecidableEq n] [DecidableEq m] in
