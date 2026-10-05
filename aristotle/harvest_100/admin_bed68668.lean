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
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- A two-qubit state: `ψ (i, j)` is the amplitude of the basis state `|i⟩ ⊗ |j⟩`.
The first factor is Alice's qubit, the second is Bob's. -/
abbrev TwoQubit := Fin 2 × Fin 2 → ℂ

/-- The Bell state `(|00⟩ + |11⟩)/√2`, shared in advance between Alice and Bob. -/
noncomputable def bell : TwoQubit :=
  fun p => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- Action of a one-qubit gate `M` on the *first* tensor factor, i.e. the operator `M ⊗ I`.
Alice can only act on her own qubit. -/
noncomputable def applyLeft (M : Matrix (Fin 2) (Fin 2) ℂ) (ψ : TwoQubit) : TwoQubit :=
  fun p => ∑ i, M p.1 i * ψ (i, p.2)

/-- The Pauli `X` (bit flip) gate. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` (phase flip) gate. -/
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Alice's encoding gate for the two-bit message `(a, b)`:
apply `X` iff `a` is true, then `Z` iff `b` is true. -/
noncomputable def encGate (a b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if b then pauliZ else 1) * (if a then pauliX else 1)

/-- Superdense coding: Alice encodes the two classical bits `(a, b)` by applying
`encGate a b` to *her own qubit only*; the resulting two-qubit state is one of the
four Bell states. -/
noncomputable def encode (a b : Bool) : TwoQubit := applyLeft (encGate a b) bell

theorem encGate_ff : encGate false false = 1 := by simp [encGate]

theorem encGate_tf : encGate true false = pauliX := by simp [encGate]

theorem encGate_ft : encGate false true = pauliZ := by simp [encGate]

theorem encGate_tt : encGate true true = !![0, 1; -1, 0] := by
  simp [encGate, pauliX, pauliZ]

/-- Each encoding gate is unitary, so Alice's operation is a legitimate quantum operation. -/
theorem encGate_unitary (a b : Bool) : (encGate a b)ᴴ * (encGate a b) = 1 := by
  cases a <;> cases b <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [encGate, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Matrix.conjTranspose_apply]

/-- The amplitudes of the encoded state are the entries of the encoding gate,
scaled by `1/√2`. -/
theorem encode_apply (a b : Bool) (j k : Fin 2) :
    encode a b (j, k) = ((1 / Real.sqrt 2 : ℝ) : ℂ) * encGate a b j k := by
  simp only [encode, applyLeft, bell]
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro i _ hik
    simp [hik]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **Superdense coding transmits two classical bits.**
The map sending a two-bit message `(a, b)` to the two-qubit state obtained by Alice
acting with `encGate a b` on her half of the shared Bell pair is injective: the four
messages give four distinct states, so after receiving Alice's single qubit Bob holds
enough information to recover both bits. -/
theorem superdense_two_bits :
    Function.Injective (fun m : Bool × Bool => encode m.1 m.2) := by
  have hc : ((1 / Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h : Real.sqrt 2 ≠ 0 := by positivity
    simp [Complex.ofReal_eq_zero, h]
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only at h
  have h00 := congrFun h (0, 0)
  have h10 := congrFun h (1, 0)
  have h11 := congrFun h (1, 1)
  rw [encode_apply, encode_apply] at h00 h10 h11
  replace h00 := mul_left_cancel₀ hc h00
  replace h10 := mul_left_cancel₀ hc h10
  replace h11 := mul_left_cancel₀ hc h11
  revert h00 h10 h11
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp only [encGate_ff, encGate_tf, encGate_ft, encGate_tt, pauliX, pauliZ] <;>
    norm_num

/-- Hermitian inner product of two two-qubit states. -/
noncomputable def inner2 (u v : TwoQubit) : ℂ := ∑ p, (starRingEnd ℂ) (u p) * v p

private theorem half_of_sqrt_two :
    ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
  have h : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← Complex.ofReal_mul, h]
  norm_num

/-- The four encoded states form an orthonormal family: Bob can distinguish them
perfectly by a measurement in the Bell basis. -/
theorem encode_orthonormal (a b a' b' : Bool) :
    inner2 (encode a b) (encode a' b') = if (a, b) = (a', b') then 1 else 0 := by
  have hc := half_of_sqrt_two
  simp only [inner2, Fintype.sum_prod_type, Fin.sum_univ_two, encode_apply, map_mul,
    Complex.conj_ofReal]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp only [encGate_ff, encGate_tf, encGate_ft, encGate_tt, pauliX, pauliZ] <;>
    norm_num [Matrix.one_apply] <;>
    ring_nf <;>
    linear_combination (norm := (push_cast [Complex.ofReal_inv]; ring_nf)) (2 : ℂ) * hc

#print axioms QC.superdense_two_bits
#print axioms QC.encode_orthonormal
#print axioms QC.encGate_unitary

end QC

