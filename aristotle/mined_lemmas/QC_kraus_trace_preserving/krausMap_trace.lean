/-
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace QC

open Matrix Finset
open scoped ComplexOrder

variable {K n : Type*} [Fintype K] [Fintype n] [DecidableEq n]

/-- The quantum channel (Kraus map) associated to a family of Kraus operators
`E : K → Matrix n n ℂ`, namely `ρ ↦ ∑ k, E k * ρ * (E k)ᴴ`. -/

theorem krausMap_trace {E : K → Matrix n n ℂ} (hE : IsKrausFamily E) (ρ : Matrix n n ℂ) :
    (krausMap E ρ).trace = ρ.trace :=
  kraus_trace_preserving E hE ρ

omit [DecidableEq n] in
/-- A Kraus map is positive: it sends positive semidefinite matrices to positive
semidefinite matrices. -/
