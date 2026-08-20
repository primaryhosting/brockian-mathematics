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

theorem isCP_of_hasKraus {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (h : HasKraus Φ) : IsCP Φ := by
  obtain ⟨V, hV⟩ := h
  intro k M hM
  set W : m × n → Matrix (Fin k × n) (Fin k × m) ℂ := fun a =>
    Matrix.of fun x y => if x.1 = y.1 then V a x.2 y.2 else 0 with hW
  have key : amp Φ k M = ∑ a, W a * M * (W a)ᴴ := by
    ext ⟨c, p⟩ ⟨d, q⟩
    simp only [amp, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hW, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      Finset.sum_ite_eq, Finset.sum_mul, mul_assoc, apply_ite (starRingEnd ℂ), mul_ite]
  rw [key]
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero fun a _ => hM.mul_mul_conjTranspose_same (W a)

omit [Fintype n] [DecidableEq n] in
/-- A completely positive map has positive semidefinite Choi matrix: the Choi matrix is, up to
reindexing, the image of the (positive semidefinite) maximally entangled state under the
amplification of `Φ`. -/
