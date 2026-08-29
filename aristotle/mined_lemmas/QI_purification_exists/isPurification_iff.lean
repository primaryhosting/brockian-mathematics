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

lemma isPurification_iff [Fintype m] (ρ : Matrix n n ℂ) (ψ : n × m → ℂ) :
    IsPurification ρ ψ ↔ coeffMatrix ψ * (coeffMatrix ψ)ᴴ = ρ := by
  rw [IsPurification, ptraceRight_pureDensity]

/-- Sanity check on the definitions: the Bell state `(|00⟩ + |11⟩)/√2` is a purification of the
maximally mixed qubit state. -/
