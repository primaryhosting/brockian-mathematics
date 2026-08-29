import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/

noncomputable def ptraceRight [Fintype m] (R : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i i' => ∑ j : m, R (i, j) (i', j)

/-- The matrix of coefficients of a vector of the composite system, i.e. the identification
of `H_A ⊗ H_B` with the space of `n × m` matrices. -/
