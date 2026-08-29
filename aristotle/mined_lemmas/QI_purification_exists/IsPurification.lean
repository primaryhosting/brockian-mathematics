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

def IsPurification [Fintype m] (ρ : Matrix n n ℂ) (ψ : n × m → ℂ) : Prop :=
  ptraceRight (pureDensity ψ) = ρ

end Defs

variable {n m : Type*}

