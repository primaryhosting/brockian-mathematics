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

theorem apply_eq_sum_choi (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) (X : Matrix m m ℂ) (p q : n) :
    Φ X p q = ∑ i, ∑ j, X i j * choiMatrix Φ (i, p) (j, q) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) by
        ext a b; simp [Matrix.single_apply]]
  rw [map_smul]
  simp [choiMatrix]

omit [DecidableEq n] in
/-- If `Φ` is given by the Kraus operators coming from `B`, then its Choi matrix is `B * Bᴴ`. -/
