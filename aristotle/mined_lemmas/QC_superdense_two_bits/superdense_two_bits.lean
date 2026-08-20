/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`;
-- the required header is reproduced verbatim as a module docstring below.)

import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## Superdense coding

Alice and Bob share the Bell pair `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` on two qubits
(state space `Fin 2 × Fin 2 → ℂ`, first component = Alice's qubit).
To send the two classical bits `(a, b)`, Alice applies the Pauli operator
`Z^b X^a` to *her* qubit only (i.e. the operator `Z^b X^a ⊗ I` acts on the pair)
and sends that single qubit to Bob.  The four resulting states are the four Bell
states, which are pairwise distinct; equivalently, the encoding map is injective,
so two classical bits are transmitted by one qubit plus prior entanglement.
-/

namespace QC

/-- Pure states of a two-qubit system (unnormalised amplitudes are allowed;
all states used here are unit vectors). -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/

theorem superdense_two_bits : Function.Injective encode := by
  rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
  have hc := sqrt2_inv_ne_zero
  have e00 : encode (a1, b1) (0, 0) = encode (a2, b2) (0, 0) := by rw [h]
  have e11 : encode (a1, b1) (1, 1) = encode (a2, b2) (1, 1) := by rw [h]
  have e10 : encode (a1, b1) (1, 0) = encode (a2, b2) (1, 0) := by rw [h]
  rw [encode_apply, encode_apply] at e00 e11 e10
  clear h
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;>
    simp [pauliOp, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] at e00 e11 e10 ⊢ <;>
    first
      | rfl
      | exact hc e00
      | exact hc e00.symm
      | exact hc (self_eq_neg.mp e11)
      | exact hc (neg_eq_self.mp e11)
      | exact hc (self_eq_neg.mp e10)
      | exact hc (neg_eq_self.mp e10)

end QC

