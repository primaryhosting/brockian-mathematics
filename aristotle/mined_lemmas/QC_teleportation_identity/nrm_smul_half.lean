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

namespace QC

/-- A qubit state: a vector of amplitudes indexed by the computational basis `{0,1}`. -/
abbrev Qubit := Fin 2 → ℂ

/-- The Pauli `X` (bit flip) gate. -/

lemma nrm_smul_half (psi : Qubit) (hpsi : nrm psi = 1) :
    nrm (fun c => (1 / 2 : ℂ) * psi c) = 1 / 2 := by
  have h : ‖psi 0‖ ^ 2 + ‖psi 1‖ ^ 2 = 1 := by
    have := hpsi
    rw [nrm] at this
    have hnn : (0:ℝ) ≤ ‖psi 0‖ ^ 2 + ‖psi 1‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnn, this]
  rw [nrm]
  have e : ‖(1 / 2 : ℂ) * psi 0‖ ^ 2 + ‖(1 / 2 : ℂ) * psi 1‖ ^ 2 = (1 / 2) ^ 2 := by
    rw [norm_mul, norm_mul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    nlinarith [h]
  rw [e, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]

/-- **Quantum teleportation.** For any qubit state `|ψ⟩` of unit norm and any Bell-measurement
outcome `(i, j)`, the state of the receiver's qubit after applying the correction `Z ^ i X ^ j`
(and renormalizing) is exactly the input state `|ψ⟩`. -/
