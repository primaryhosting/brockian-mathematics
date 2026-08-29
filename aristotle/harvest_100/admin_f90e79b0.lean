/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module doc-comment `/-! ... -/`, so the
-- header above is written as a plain block comment with identical text.)

import Mathlib

/-!
## Superdense coding

Alice and Bob share the Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` in `ℂ² ⊗ ℂ²`.  We represent a
two-qubit state as a `2 × 2` complex matrix `M`, where `M i j` is the amplitude of `|i j⟩`;
in this picture `|Φ⁺⟩` is `(√2)⁻¹ • 1` and acting by a unitary `U` on Alice's (first) qubit is
left multiplication `U * M`.

To send the two classical bits `(b₁, b₂)` Alice applies the Pauli operator `Z^b₁ X^b₂` to her
single qubit and sends it to Bob.  The resulting four states are the four Bell states; we show
they are orthonormal (`QC.encode_orthonormal`) and hence that the encoding is injective on the
four messages (`QC.superdense_two_bits`): two classical bits have been transmitted through one
qubit plus prior entanglement.  A decoder therefore exists (`QC.exists_decoder`).
-/

namespace QC

open Matrix

/-- The Pauli `X` gate. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate. -/
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The encoding gate `Z^b₁ X^b₂` that Alice applies to her qubit. -/
noncomputable def pauli (b₁ b₂ : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if b₁ then pauliZ else 1) * (if b₂ then pauliX else 1)

/-- The shared Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, as a `2 × 2` amplitude matrix. -/
noncomputable def bell : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • 1

/-- Superdense encoding: the two-qubit state obtained by applying `Z^b₁ X^b₂` to Alice's half
of the Bell pair. -/
noncomputable def encode (m : Bool × Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauli m.1 m.2 * bell

/-- The Hilbert–Schmidt inner product, which is the usual inner product of the two-qubit
states under the matrix representation. -/
noncomputable def ip (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := Matrix.trace (Aᴴ * B)

lemma encode_eq (m : Bool × Bool) :
    encode m = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • pauli m.1 m.2 := by
  simp [encode, bell]

/-- The four encoding gates are orthogonal with respect to the Hilbert–Schmidt inner product. -/
theorem pauli_trace (a b c d : Bool) :
    Matrix.trace ((pauli a b)ᴴ * pauli c d) = if (a = c ∧ b = d) then 2 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [pauli, pauliX, pauliZ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_fin_two]

/-- The four encoded states are orthonormal. -/
theorem encode_orthonormal (m m' : Bool × Bool) :
    ip (encode m) (encode m') = if m = m' then 1 else 0 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  obtain ⟨a, b⟩ := m
  obtain ⟨c, d⟩ := m'
  rw [ip, encode_eq, encode_eq, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, pauli_trace]
  have hstar : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  simp only [smul_eq_mul, hstar, ← mul_assoc, hs]
  by_cases h : a = c ∧ b = d
  · rw [if_pos h, if_pos (by simp [h])]
    norm_num
  · rw [if_neg h, if_neg (by simpa [Prod.ext_iff] using h)]
    ring

/-- **Superdense coding transmits two classical bits.**  The map sending a two-bit message
`(b₁, b₂)` to the two-qubit state obtained by applying `Z^b₁ X^b₂` to Alice's single qubit of a
shared Bell pair is injective on the four messages. -/
theorem superdense_two_bits : Function.Injective encode := by
  intro m m' h
  by_contra hne
  have h0 : ip (encode m) (encode m') = 0 := by
    rw [encode_orthonormal, if_neg hne]
  rw [h, encode_orthonormal, if_pos rfl] at h0
  exact one_ne_zero h0

/-- Consequently Bob can decode: there is a map recovering the two classical bits from the
received two-qubit state. -/
theorem exists_decoder : ∃ decode : Matrix (Fin 2) (Fin 2) ℂ → Bool × Bool,
    ∀ m, decode (encode m) = m :=
  ⟨Function.invFun encode, fun m => superdense_two_bits (Function.invFun_eq ⟨m, rfl⟩)⟩

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

