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

def amp (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) (k : ℕ)
    (M : Matrix (Fin k × m) (Fin k × m) ℂ) : Matrix (Fin k × n) (Fin k × n) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => M (p.1, i) (q.1, j)) p.2 q.2

/-- A linear map between matrix algebras is *completely positive* if all its amplifications
`id_{Fin k} ⊗ Φ` map positive semidefinite matrices to positive semidefinite matrices. -/
