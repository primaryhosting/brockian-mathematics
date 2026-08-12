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

/-!
# Superdense coding

Superdense coding: Alice and Bob share the maximally entangled two-qubit state
`|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.  To send two classical bits `(a, b)` Alice applies the local
unitary `Z^a X^b` to *her* qubit only (the first tensor factor) and sends that single qubit
to Bob.  The four resulting global states are the four Bell states.

We model a two-qubit pure state as a function `Fin 2 × Fin 2 → ℂ` (amplitudes in the
computational basis) and Alice's local operation as left multiplication of the first index
by a `2 × 2` matrix.

The main result `QC.superdense_two_bits` says that the encoding of the four messages
(elements of `Bool × Bool`, i.e. two classical bits) is injective; `QC.encode_orthonormal`
strengthens this to: the four encoded states are orthonormal, hence perfectly
distinguishable by Bob, so two classical bits are indeed transmitted.
-/

namespace QC

open Matrix

/-- The Pauli `X` matrix. -/
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The shared maximally entangled state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, given by its amplitudes
in the computational basis of two qubits. -/
noncomputable def bell (p : Fin 2 × Fin 2) : ℂ :=
  if p.1 = p.2 then ((1 : ℝ) / Real.sqrt 2 : ℝ) else 0

/-- Alice's local encoding unitary for the message `m = (a, b)`: `Z^a X^b`. -/
noncomputable def encU (m : Bool × Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if m.1 then PZ else 1) * (if m.2 then PX else 1)

/-- Alice's encoding operations are unitary. -/
theorem encU_unitary (m : Bool × Bool) : encU m * (encU m)ᴴ = 1 := by
  obtain ⟨a, b⟩ := m
  cases a <;> cases b <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [encU, PX, PZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The encoded two-qubit state: Alice applies `Z^a X^b` to the first qubit of `|Φ⁺⟩`.
These are exactly the four Bell states. -/
noncomputable def encode (m : Bool × Bool) (p : Fin 2 × Fin 2) : ℂ :=
  ∑ j : Fin 2, encU m p.1 j * bell (j, p.2)

lemma encode_apply (m : Bool × Bool) (i k : Fin 2) :
    encode m (i, k) = encU m i k * ((1 : ℝ) / Real.sqrt 2 : ℝ) := by
  simp [encode, bell]

lemma sqrt2_inv_ne_zero : ((((1 : ℝ) / Real.sqrt 2 : ℝ)) : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp [h.ne']

lemma sqrt2_inv_sq :
    ((((1 : ℝ) / Real.sqrt 2 : ℝ)) : ℂ) * (((1 : ℝ) / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul]
  have h : ((1 : ℝ) / Real.sqrt 2) * ((1 : ℝ) / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [h]
  norm_num

/-- **Superdense coding**: the encoding of the four two-bit messages into the single qubit
Alice sends (equivalently, into the resulting global two-qubit state) is injective, so two
classical bits are transmitted by one qubit plus prior entanglement. -/
theorem superdense_two_bits : Function.Injective encode := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have key : ∀ i k : Fin 2, encU (a, b) i k = encU (c, d) i k := by
    intro i k
    have hik := congrFun h (i, k)
    rw [encode_apply, encode_apply] at hik
    exact mul_right_cancel₀ sqrt2_inv_ne_zero hik
  have k00 := key 0 0
  have k10 := key 1 0
  have k11 := key 1 1
  clear h key
  revert k00 k10 k11
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [encU, PX, PZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The four encoded states are orthonormal, hence perfectly distinguishable by Bob:
he recovers both classical bits with certainty. -/
theorem encode_orthonormal (m m' : Bool × Bool) :
    ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (encode m p) * encode m' p
      = if m = m' then 1 else 0 := by
  obtain ⟨a, b⟩ := m
  obtain ⟨c, d⟩ := m'
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, encode_apply]
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [encU, PX, PZ, Matrix.mul_apply, Fin.sum_univ_two, sqrt2_inv_sq,
      Complex.ext_iff] <;> ring_nf <;> norm_num [sqrt2_inv_sq]

end QC

#print axioms QC.superdense_two_bits
#print axioms QC.encode_orthonormal
#print axioms QC.encU_unitary

