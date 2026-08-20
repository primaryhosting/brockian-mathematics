/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

theorem shor_error_scales_inner (k : Idx) (M : Bool → Bool → ℂ) :
    ∃ w : ℂ, ∀ co co' : Bool → ℂ,
      ip (applyOp k M (codeState co)) (applyOp k M (codeState co'))
        = w * ip (codeState co) (codeState co') := by
  obtain ⟨w, hw⟩ := shor_code_corrects.2 k k M M
  refine ⟨w, fun co co' => ?_⟩
  have hA : ∀ c : Bool → ℂ,
      applyOp k M (codeState c) = fun v => ∑ s : Bool, c s * applyOp k M (psi s) v := by
    intro c
    exact applyOp_sum k M c psi
  rw [hA, hA]
  rw [ip_sum_sum (fun s => fun v => co s * applyOp k M (psi s) v)
    (fun t => fun v => co' t * applyOp k M (psi t) v)]
  unfold codeState
  rw [ip_sum_sum (fun s => fun v => co s * psi s v) (fun t => fun v => co' t * psi t v)]
  simp only [ip_smul_smul, hw, ip_psi]
  simp
  ring

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

