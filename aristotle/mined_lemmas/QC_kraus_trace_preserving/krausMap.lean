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

noncomputable def krausMap (E : K → Matrix n n ℂ) (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, E k * ρ * (E k)ᴴ

/-- The Kraus completeness (trace-preservation) relation `∑ k, (E k)ᴴ * (E k) = I`. -/
