/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` lines to
-- precede any module docstring; the same text is repeated verbatim below.)
import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ(ℂ) →ₗ Mₘ(ℂ)`:
`C (i,k) (j,l) = (Φ Eᵢⱼ) k l`, where the `Eᵢⱼ` are the matrix units. -/

private lemma matrix_conj_apply (W : Matrix m n ℂ) (X : Matrix n n ℂ) (k l : m) :
    (W * X * Wᴴ) k l = ∑ i, ∑ j, X i j * (W k i * (starRingEnd ℂ) (W l j)) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc, mul_left_comm]
  exact Finset.sum_comm

section

variable (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)

omit [DecidableEq n] [DecidableEq m] in
/-- A map given by a Kraus decomposition is completely positive. -/
