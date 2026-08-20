import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder MatrixOrder

namespace QI

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The partial trace over the second (environment) tensor factor. -/

noncomputable def ptraceRight {B E : Type} [Fintype E] (M : Matrix (B × E) (B × E) ℂ) :
    Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ x : E, M (b, x) (b', x)

/-- Complete positivity of a linear map between matrix algebras: for every `k`, the
amplified map `id_{Fin k} ⊗ Φ` sends positive semidefinite matrices to positive
semidefinite matrices. -/
