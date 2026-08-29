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

def IsDensityMatrix (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- **Kraus maps are trace preserving.**
If a family of Kraus operators `E : K → Matrix n n ℂ` satisfies the completeness
relation `∑ k, (E k)ᴴ * E k = 1`, then the associated quantum channel
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace. -/
