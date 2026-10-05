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

theorem krausMap_isDensityMatrix {E : K → Matrix n n ℂ} (hE : IsKrausFamily E)
    {ρ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (krausMap E ρ) :=
  ⟨krausMap_posSemidef E hρ.1, (krausMap_trace hE ρ).trans hρ.2⟩

end QC

