/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- The amplitude `1/√2` of a maximally entangled two-qubit state. -/
noncomputable def amp : ℂ := 1 / (Real.sqrt 2 : ℝ)

/-- The shared entangled resource `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`,
described by its amplitudes on the computational basis of two qubits. -/
noncomputable def bell : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then amp else 0

/-- The Pauli `X` gate. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Alice's encoding gate for the two classical bits `a` and `b`: `X^b Z^a`,
applied to her half of the entangled pair. -/
noncomputable def encOp (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliX ^ (b : ℕ) * pauliZ ^ (a : ℕ)

/-- The two-qubit state held jointly by Alice and Bob after Alice applies
`X^b Z^a ⊗ I` to `|Φ⁺⟩`; sending her single qubit to Bob conveys the message. -/
noncomputable def encode (m : Fin 2 × Fin 2) : Fin 2 × Fin 2 → ℂ :=
  fun p => ∑ k : Fin 2, encOp m.1 m.2 p.1 k * bell (k, p.2)

lemma amp_ne_zero : amp ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp only [amp, ne_eq, div_eq_zero_iff]
  simp only [one_ne_zero, false_or, Complex.ofReal_eq_zero]
  exact_mod_cast h.ne'

lemma amp_sq : amp * amp = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h2
  rw [amp, one_div_mul_one_div, h]

/-- The four encoded states are exactly the four Bell states. -/
lemma encode_apply (a b : Fin 2) (p : Fin 2 × Fin 2) :
    encode (a, b) p =
      (if p.1 = b + p.2 then (if a = 1 ∧ p.2 = 1 then -amp else amp) else 0) := by
  fin_cases a <;> fin_cases b <;>
    obtain ⟨i, j⟩ := p <;> fin_cases i <;> fin_cases j <;>
      simp [encode, encOp, pauliX, pauliZ, bell, Matrix.mul_apply, Fin.sum_univ_two,
        pow_succ, Matrix.one_apply]

/-- **Superdense coding transmits two classical bits.**
Alice's encoding `(a, b) ↦ (X^b Z^a ⊗ I)|Φ⁺⟩`, which acts on her single qubit only,
is injective on the four two-bit messages, so Bob can recover both bits. -/
theorem superdense_two_bits : Function.Injective encode := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h00 := congrFun h (0, 0)
  have h01 := congrFun h (0, 1)
  have h10 := congrFun h (1, 0)
  have h11 := congrFun h (1, 1)
  simp only [encode_apply] at h00 h01 h10 h11
  have hz := amp_ne_zero
  have hnz : (amp : ℂ) ≠ -amp := by
    intro hc
    apply hz
    have h2a : (2 : ℂ) * amp = 0 := by linear_combination hc
    simpa using (mul_eq_zero.mp h2a).resolve_left (by norm_num)
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp_all

/-- The four encoded states are orthonormal, hence perfectly distinguishable by Bob:
the inner product of the states for messages `m` and `m'` is `1` if `m = m'` and `0` otherwise. -/
theorem superdense_orthonormal (m m' : Fin 2 × Fin 2) :
    (∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (encode m p) * encode m' p) =
      if m = m' then 1 else 0 := by
  have hstar : (starRingEnd ℂ) amp = amp := by
    simp [amp, Complex.conj_ofReal]
  obtain ⟨a, b⟩ := m
  obtain ⟨a', b'⟩ := m'
  have hsum : ∀ f : Fin 2 × Fin 2 → ℂ,
      (∑ p : Fin 2 × Fin 2, f p) = f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
    intro f
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc]
  rw [hsum]
  simp only [encode_apply]
  have h2 : amp * amp = 1 / 2 := amp_sq
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [hstar] <;> linear_combination (2 : ℂ) * h2

end QC

