import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped MatrixOrder ComplexOrder

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The ampliation `id_d ⊗ Φ` of a linear map `Φ` between matrix algebras, described
blockwise: the `(a, b)` block of the output is `Φ` applied to the `(a, b)` block of the input. -/

def amp (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {d : Type} (M : Matrix (d × n) (d × n) ℂ) :
    Matrix (d × m) (d × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => M (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive: every ampliation `id_d ⊗ Φ` maps positive semidefinite
matrices to positive semidefinite matrices. -/
