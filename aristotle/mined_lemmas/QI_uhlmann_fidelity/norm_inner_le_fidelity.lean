/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions

We work with a finite dimensional quantum system with Hilbert space `EuclideanSpace ℂ n`.
States are described by positive semidefinite matrices, and a purification of a state `ρ`
on the system is a vector of the composite system `EuclideanSpace ℂ (n × m)` (the tensor
product of the system with an ancilla) whose reduced density matrix (the partial trace over
the ancilla) is `ρ`.
-/

/-- The partial trace over the second (ancilla) tensor factor. -/

theorem norm_inner_le_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {v w : EuclideanSpace ℂ (n × m)} (hv : IsPurification v ρ) (hw : IsPurification w σ) :
    ‖(inner ℂ v w : ℂ)‖ ≤ fidelity ρ σ := by
  have hv' : vecToMat v * (vecToMat v)ᴴ = ρ := by
    rw [← isPurification_matToVec_iff, matToVec_vecToMat]; exact hv
  have hw' : vecToMat w * (vecToMat w)ᴴ = σ := by
    rw [← isPurification_matToVec_iff, matToVec_vecToMat]; exact hw
  have hle := norm_trace_le_fidelity hρ hσ hv' hw'
  rwa [← inner_matToVec, matToVec_vecToMat, matToVec_vecToMat] at hle

end QI

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

