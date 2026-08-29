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

theorem krausMap_posSemidef (E : K → Matrix n n ℂ) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (krausMap E ρ).PosSemidef :=
  Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun k _ => hρ.mul_mul_conjTranspose_same (E k))

/-- A CPTP Kraus channel maps density matrices to density matrices. -/
