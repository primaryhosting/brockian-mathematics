import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
it applies `Φ` to each `n × n` block of a `(k × n) × (k × n)` matrix. -/

def amplify (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (k : Type) [Fintype k]
    (M : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => M (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive: every amplification `id_k ⊗ Φ` maps positive
semidefinite matrices to positive semidefinite matrices. -/
