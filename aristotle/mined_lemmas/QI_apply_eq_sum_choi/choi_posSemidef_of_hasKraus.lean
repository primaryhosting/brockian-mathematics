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

theorem choi_posSemidef_of_hasKraus {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (h : HasKraus Φ) :
    (choiMatrix Φ).PosSemidef := by
  obtain ⟨V, hV⟩ := h
  set B : Matrix (m × n) (m × n) ℂ := Matrix.of fun p a => V a p.2 p.1 with hB
  have hkr : krausMat B = V := by
    funext a; ext k i; simp [krausMat, hB]
  rw [choi_eq_of_krausMat Φ B (by rw [hkr]; exact hV)]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- A map with positive semidefinite Choi matrix admits a Kraus decomposition. -/
