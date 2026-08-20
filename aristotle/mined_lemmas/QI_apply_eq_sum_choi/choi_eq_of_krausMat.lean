/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The Choi–Jamiołkowski isomorphism

For a linear map `Φ` between finite-dimensional matrix algebras we prove that the following
are equivalent:

* `Φ` is completely positive (`QI.IsCP`), i.e. all amplifications `id ⊗ Φ` preserve positive
  semidefiniteness;
* the Choi matrix of `Φ` (`QI.choiMatrix`) is positive semidefinite;
* `Φ` admits a Kraus decomposition (`QI.HasKraus`).

The main statement is `QI.choi_jamiolkowski`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The amplification `id_{Fin k} ⊗ Φ` of a linear map `Φ` on matrices: it applies `Φ` to each
`m × m` block of a `(Fin k × m) × (Fin k × m)` matrix. -/

private theorem choi_eq_of_krausMat (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (B : Matrix (m × n) (m × n) ℂ)
    (h : ∀ X, Φ X = ∑ a, krausMat B a * X * (krausMat B a)ᴴ) : choiMatrix Φ = B * Bᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [choiMatrix, Matrix.of_apply, h, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun a _ => conj_single (krausMat B a) i j k l

omit [DecidableEq n] in
/-- If the Choi matrix of `Φ` factors as `B * Bᴴ`, then `B` provides Kraus operators for `Φ`. -/
