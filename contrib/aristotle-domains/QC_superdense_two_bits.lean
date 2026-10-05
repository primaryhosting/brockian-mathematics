/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Statement: Superdense coding transmits 2 classical bits via 1 qubit + prior entanglement (encoding is injective on the 4 messages).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix
open scoped Kronecker

/-- A two–qubit state vector, indexed by a pair of bits. -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The local unitary Alice applies to encode the message `m = (a, b)`: `X ^ a * Z ^ b`. -/
noncomputable def encodeOp (m : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliX ^ (m.1 : ℕ) * pauliZ ^ (m.2 : ℕ)

/-- The Bell state `|Φ+⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bell : TwoQubit := fun p => if p.1 = p.2 then ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- The state of the entangled pair after Alice encodes the message `m` by acting
on her qubit alone. -/
noncomputable def encode (m : Fin 2 × Fin 2) : TwoQubit :=
  (encodeOp m ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ bell

/-- The Hermitian inner product on two–qubit states. -/
noncomputable def ip (v w : TwoQubit) : ℂ := ∑ p : Fin 2 × Fin 2, star (v p) * w p

private theorem coeff_sq : (((Real.sqrt 2 : ℝ)) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [inv_pow, h]
  norm_num

/-- Explicit entries: `(U ⊗ I)|Φ+⟩` has entries `U i j / √2`. -/
theorem encode_apply (m : Fin 2 × Fin 2) (i j : Fin 2) :
    encode m (i, j) = ((Real.sqrt 2)⁻¹ : ℝ) * encodeOp m i j := by
  simp only [encode, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, bell, Matrix.one_apply]
  simp
  ring

/-- Alice's encoding operations are unitary, hence legal local operations. -/
theorem encodeOp_unitary (m : Fin 2 × Fin 2) : (encodeOp m)ᴴ * encodeOp m = 1 := by
  fin_cases m <;>
    simp [encodeOp, pauliX, pauliZ, ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

/-- Distinct two–bit messages give orthogonal states, so Bob can distinguish them
perfectly with a (Bell basis) measurement. -/
theorem encode_orthogonal {m m' : Fin 2 × Fin 2} (h : m ≠ m') :
    ip (encode m) (encode m') = 0 := by
  simp only [ip, Fintype.sum_prod_type, Fin.sum_univ_two, encode_apply]
  fin_cases m <;> fin_cases m' <;>
    simp_all [encodeOp, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Each encoded state is a unit vector. -/
theorem encode_normalized (m : Fin 2 × Fin 2) : ip (encode m) (encode m) = 1 := by
  simp only [ip, Fintype.sum_prod_type, Fin.sum_univ_two, encode_apply]
  fin_cases m <;>
    simp_all [encodeOp, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [coeff_sq] <;> norm_num

/-- **Superdense coding**: two classical bits are transmitted using one qubit plus
prior entanglement — encoding the four two–bit messages by local Pauli operations
on Alice's half of a Bell pair is injective (indeed the four resulting states are
orthonormal, so Bob recovers the message exactly). -/
theorem superdense_two_bits : Function.Injective encode := by
  intro m m' h
  by_contra hne
  have h0 : ip (encode m) (encode m') = 0 := encode_orthogonal hne
  rw [h, encode_normalized m'] at h0
  exact one_ne_zero h0

end QC


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

