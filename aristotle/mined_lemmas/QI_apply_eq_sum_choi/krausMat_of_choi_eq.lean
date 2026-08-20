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

private theorem krausMat_of_choi_eq (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (B : Matrix (m × n) (m × n) ℂ) (h : choiMatrix Φ = B * Bᴴ) :
    ∀ X, Φ X = ∑ a, krausMat B a * X * (krausMat B a)ᴴ := by
  intro X
  ext p q
  rw [apply_eq_sum_choi Φ X p q]
  calc ∑ i, ∑ j, X i j * choiMatrix Φ (i, p) (j, q)
      = ∑ i, ∑ j, ∑ a, X i j * (B (i, p) a * star (B (j, q) a)) := by
        simp only [h, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
    _ = ∑ j, ∑ i, ∑ a, X i j * (B (i, p) a * star (B (j, q) a)) := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, X i j * (B (i, p) a * star (B (j, q) a)) := sum_comm3 _
    _ = (∑ a, krausMat B a * X * (krausMat B a)ᴴ) p q := by
        simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, krausMat,
          Matrix.of_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq n] in
/-- A map given by a Kraus decomposition has positive semidefinite Choi matrix. -/
