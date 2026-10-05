/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command of a file, so the header above is a
-- plain block comment; the identical text is repeated below as the module docstring.)

import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
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

/-! ## Basic notions

A qubit state is an amplitude vector indexed by `Fin 2`; a three-qubit register state is
an amplitude array indexed by `Fin 2 × Fin 2 × Fin 2` (written in curried form).
Addition on `Fin 2` is exactly the XOR of classical bits.

Mathlib has no development of the quantum teleportation protocol (there is no lemma that
`exact?`/`rw?` can apply here), so the protocol is set up from scratch below; the proof
itself only uses `Real.mul_self_sqrt` from Mathlib together with ring normalisation. -/

/-- Amplitude vector of a single qubit. -/
abbrev Qubit : Type := Fin 2 → ℂ

/-- Amplitude array of a three-qubit register. -/
abbrev State3 : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The normalisation constant `1/√2`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [invSqrt2, ← mul_inv, h]
  norm_num

lemma norm_invSqrt2_pow_four : ‖invSqrt2‖ ^ 4 = 1 / 4 := by
  have h2 : ‖invSqrt2‖ ^ 2 = 1 / 2 := by
    rw [sq, ← norm_mul, invSqrt2_mul_self]; norm_num
  have h4 : ‖invSqrt2‖ ^ 4 = (‖invSqrt2‖ ^ 2) ^ 2 := by ring
  rw [h4, h2]; norm_num

/-- The sign `(-1)^b` attached to a bit `b`. -/
def sign : Fin 2 → ℂ
  | 0 => 1
  | 1 => -1

@[simp] lemma sign_zero : sign 0 = 1 := rfl
@[simp] lemma sign_one : sign 1 = -1 := rfl

@[simp] lemma norm_sign (m : Fin 2) : ‖sign m‖ = 1 := by fin_cases m <;> simp [sign]

/-! ## Single-qubit gates -/

/-- Pauli `X` (bit flip): `X|c⟩ = |c ⊕ 1⟩`, i.e. the two amplitudes are swapped. -/
def pauliX (q : Qubit) : Qubit := fun c => q (c + 1)

/-- Pauli `Z` (phase flip): `Z|c⟩ = (-1)^c |c⟩`. -/
def pauliZ (q : Qubit) : Qubit := fun c => sign c * q c

/-- `X^m` for a classical bit `m`. -/
def pauliXpow (m : Fin 2) (q : Qubit) : Qubit := if m = 1 then pauliX q else q

/-- `Z^m` for a classical bit `m`. -/
def pauliZpow (m : Fin 2) (q : Qubit) : Qubit := if m = 1 then pauliZ q else q

/-! ## The protocol -/

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` shared by Alice (qubit 2) and Bob (qubit 3). -/
noncomputable def bell : Fin 2 → Fin 2 → ℂ := fun b c => if b = c then invSqrt2 else 0

/-- The initial three-qubit state `|ψ⟩ ⊗ |Φ⁺⟩`. -/
noncomputable def initial (psi : Qubit) : State3 := fun a b c => psi a * bell b c

/-- CNOT with control qubit 1 and target qubit 2.  Since the basis permutation
`|a, b, c⟩ ↦ |a, b ⊕ a, c⟩` is an involution, the amplitudes transform by the same
permutation. -/
def cnot12 (P : State3) : State3 := fun a b c => P a (b + a) c

/-- Hadamard on qubit 1; its matrix entries are `H a x = (1/√2) (-1)^(a·x)`. -/
noncomputable def hadamard1 (P : State3) : State3 :=
  fun a b c => invSqrt2 * (P 0 b c + sign a * P 1 b c)

/-- The state just before Alice's measurement:
`(H ⊗ I ⊗ I) (CNOT₁₂ ⊗ I) (|ψ⟩ ⊗ |Φ⁺⟩)`. -/
noncomputable def preMeasurement (psi : Qubit) : State3 :=
  hadamard1 (cnot12 (initial psi))

/-- The (unnormalised) state of Bob's qubit after Alice measures qubits 1 and 2 in the
computational basis and obtains the outcomes `m₁, m₂`. -/
noncomputable def branch (psi : Qubit) (m1 m2 : Fin 2) : Qubit :=
  fun c => preMeasurement psi m1 m2 c

/-- Each of the four measurement outcomes occurs with probability `1/4`: the squared norm
of the corresponding branch is `1/4` of that of the input state.  This is what justifies
the normalisation factor `2` used in `QC.corrected`. -/
lemma branch_normSq (psi : Qubit) (m1 m2 : Fin 2) :
    ∑ c : Fin 2, ‖branch psi m1 m2 c‖ ^ 2 = (1 / 4) * ∑ c : Fin 2, ‖psi c‖ ^ 2 := by
  have hn := norm_invSqrt2_pow_four
  fin_cases m1 <;> fin_cases m2 <;>
    simp [branch, preMeasurement, hadamard1, cnot12, initial, bell, Fin.sum_univ_two,
      mul_comm, mul_pow] <;>
    linear_combination (‖psi 0‖ ^ 2 + ‖psi 1‖ ^ 2) * hn

/-- Bob's correction `Z^{m₁} X^{m₂}`, applied to the normalised post-measurement state of
his qubit (the branch rescaled by `2`, cf. `QC.branch_normSq`). -/
noncomputable def corrected (psi : Qubit) (m1 m2 : Fin 2) : Qubit :=
  pauliZpow m1 (pauliXpow m2 ((2 : ℂ) • branch psi m1 m2))

/-- **Teleportation identity.**  For every input qubit state `|ψ⟩` and every pair of
classical measurement outcomes `(m₁, m₂)` obtained by Alice, the post-correction state of
Bob's qubit, obtained by applying `Z^{m₁} X^{m₂}`, is exactly the input state `|ψ⟩`. -/
theorem teleportation_identity (psi : Qubit) (m1 m2 : Fin 2) :
    corrected psi m1 m2 = psi := by
  have hs := invSqrt2_mul_self
  funext c
  fin_cases m1 <;> fin_cases m2 <;> fin_cases c <;>
    simp [corrected, branch, preMeasurement, hadamard1, cnot12, initial, bell,
      pauliZpow, pauliXpow, pauliX, pauliZ, sign] <;>
    first
      | linear_combination (-2 * psi 0) * hs
      | linear_combination (-2 * psi 1) * hs
      | linear_combination (2 * psi 0) * hs
      | linear_combination (2 * psi 1) * hs

end QC

#print axioms QC.teleportation_identity

