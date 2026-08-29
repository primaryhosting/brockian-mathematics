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

lemma ptraceRight_pureDensity [Fintype m] (ψ : n × m → ℂ) :
    ptraceRight (pureDensity ψ) = coeffMatrix ψ * (coeffMatrix ψ)ᴴ := by
  ext i i'
  simp [ptraceRight, pureDensity, coeffMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]

