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

/-
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian (density) matrix `ρ`,
computed in the eigenbasis: `S(ρ) = ∑ i, -λ i * log (λ i)` where `λ` are the eigenvalues
of `ρ`. -/

theorem isPureState_basis (i : n) :
    IsPureState (Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ)))) := by
  refine ⟨Pi.single i (1 : ℂ), ?_, rfl⟩
  simp [Pi.single_apply, apply_ite (fun z : ℂ => ‖z‖ ^ 2)]

/-- The von Neumann entropy of the computational basis state `|i⟩⟨i|` is `0`. -/
