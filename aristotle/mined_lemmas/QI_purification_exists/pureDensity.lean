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

def pureDensity (ψ : n × m → ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => ψ p * star (ψ q)

/-- The partial trace over the second (ancilla) tensor factor. -/
