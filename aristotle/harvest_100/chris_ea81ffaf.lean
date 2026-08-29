/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

noncomputable section

/-- Pauli `X` gate. -/
def sx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Z` gate. -/
def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The encoding gate applied by Alice to her qubit for the message `(a, b)`. -/
def pauli (a b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if a then sx else 1) * (if b then sz else 1)

/-- The normalization constant `1/√2`. -/
def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_ne_zero : invSqrt2 ≠ 0 := by
  simp [invSqrt2]

/-- The Bell state `(|00⟩ + |11⟩)/√2` on two qubits. -/
def bell : (Fin 2 × Fin 2) → ℂ := fun p => if p.1 = p.2 then invSqrt2 else 0

/-- Superdense coding encoding: Alice applies `pauli a b` to her half of the shared
Bell pair (identity acts on Bob's half) and sends her single qubit to Bob. -/
def encode (a b : Bool) : (Fin 2 × Fin 2) → ℂ :=
  (Matrix.kroneckerMap (· * ·) (pauli a b) (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ bell

lemma encode_apply (a b : Bool) (i j : Fin 2) :
    encode a b (i, j) = pauli a b i j * invSqrt2 := by
  classical
  simp only [encode, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, bell,
    Fintype.sum_prod_type, Matrix.one_apply]
  simp [Finset.sum_ite_eq', mul_comm]

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  rw [invSqrt2, ← mul_inv, ← Complex.ofReal_mul, h]
  norm_num

/-- The four encoded states are orthonormal, so Bob can perfectly distinguish them
(a Bell-basis measurement recovers both classical bits). -/
theorem encode_inner (a b c d : Bool) :
    ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (encode a b p) * encode c d p =
      if (a, b) = (c, d) then 1 else 0 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, encode_apply]
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [pauli, sx, sz, conj_invSqrt2, invSqrt2_mul_self, mul_comm] <;>
    ring

/-- **Superdense coding transmits two classical bits.**
The four encodings of the two-bit messages are pairwise distinct states of the
two-qubit system, i.e. the encoding map is injective on the four messages. -/
theorem superdense_two_bits :
    Function.Injective (fun p : Bool × Bool => encode p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h00 := congrFun h (0, 0)
  have h01 := congrFun h (0, 1)
  have h11 := congrFun h (1, 1)
  simp only [encode_apply] at h00 h01 h11
  have hc := invSqrt2_ne_zero
  have hc2 : invSqrt2 ≠ -invSqrt2 := fun h => invSqrt2_ne_zero (by linear_combination h / 2)
  revert h00 h01 h11
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [pauli, sx, sz, hc, hc2, Ne.symm hc2]

end

end QC

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

