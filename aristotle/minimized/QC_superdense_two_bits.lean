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
noncomputable def bellPhiPlus : TwoQubit :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- The Pauli `X` (bit flip) matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` (phase flip) matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The encoding unitary `Z^b X^a` that Alice applies to her qubit for the
message `m = (a, b)`. -/
noncomputable def pauliOp (m : Bool × Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if m.2 then pauliZ else 1) * (if m.1 then pauliX else 1)

/-- Superdense encoding: apply `(Z^b X^a) ⊗ I` to the shared Bell pair. -/
noncomputable def encode (m : Bool × Bool) : TwoQubit :=
  fun p => ∑ k : Fin 2, pauliOp m p.1 k * bellPhiPlus (k, p.2)

/-- The amplitudes of the encoded state are exactly the entries of the Pauli
operator, scaled by `1/√2`. -/
lemma encode_apply (m : Bool × Bool) (i j : Fin 2) :
    encode m (i, j) = pauliOp m i j * ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [encode, bellPhiPlus]

lemma sqrt2_inv_ne_zero : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by simp

/-- **Superdense coding transmits two classical bits.**  The encoding map
sending a two-bit message `(a, b)` to the two-qubit state obtained by applying
`(Z^b X^a) ⊗ I` to the shared Bell pair `|Φ⁺⟩` is injective on the four
messages, so Bob can recover both bits from the single qubit Alice sends
together with his half of the entangled pair. -/
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

