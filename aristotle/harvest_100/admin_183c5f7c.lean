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
def IsKrausFamily (E : K → Matrix n n ℂ) : Prop :=
  ∑ k, (E k)ᴴ * E k = 1

/-- A matrix is a density matrix when it is positive semidefinite with unit trace. -/
def IsDensityMatrix (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- **Kraus maps are trace preserving.**
If a family of Kraus operators `E : K → Matrix n n ℂ` satisfies the completeness
relation `∑ k, (E k)ᴴ * E k = 1`, then the associated quantum channel
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace. -/
theorem kraus_trace_preserving
    (E : K → Matrix n n ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (ρ : Matrix n n ℂ) :
    Matrix.trace (∑ k, E k * ρ * (E k)ᴴ) = Matrix.trace ρ := by
  rw [Matrix.trace_sum]
  have hstep : ∀ k, Matrix.trace (E k * ρ * (E k)ᴴ)
      = Matrix.trace ((E k)ᴴ * E k * ρ) := fun k => Matrix.trace_mul_cycle _ _ _
  simp only [hstep]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hE, Matrix.one_mul]

/-- Restatement of trace preservation in terms of `krausMap` and `IsKrausFamily`. -/
theorem krausMap_trace {E : K → Matrix n n ℂ} (hE : IsKrausFamily E) (ρ : Matrix n n ℂ) :
    (krausMap E ρ).trace = ρ.trace :=
  kraus_trace_preserving E hE ρ

omit [DecidableEq n] in
/-- A Kraus map is positive: it sends positive semidefinite matrices to positive
semidefinite matrices. -/
theorem krausMap_posSemidef (E : K → Matrix n n ℂ) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (krausMap E ρ).PosSemidef :=
  Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun k _ => hρ.mul_mul_conjTranspose_same (E k))

/-- A CPTP Kraus channel maps density matrices to density matrices. -/
theorem krausMap_isDensityMatrix {E : K → Matrix n n ℂ} (hE : IsKrausFamily E)
    {ρ : Matrix n n ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (krausMap E ρ) :=
  ⟨krausMap_posSemidef E hρ.1, (krausMap_trace hE ρ).trans hρ.2⟩

end QC

