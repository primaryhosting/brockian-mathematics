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

/-! ## Setup

A qubit state is a vector of amplitudes indexed by `Fin 2`.  Addition on `Fin 2`
is addition modulo `2`, i.e. the classical `xor` used to describe the Pauli `X`
gate and the Bell basis.
-/

/-- The amplitude `1/√2`, as a complex number. -/
noncomputable def isqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

@[simp] lemma isqrt2_mul_isqrt2 : isqrt2 * isqrt2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [isqrt2, ← mul_inv, h]
  norm_num

/-- Normalisation bookkeeping: the two factors of `1/√2` cancel the
renormalisation factor `2`. -/
lemma two_mul_isqrt2_mul (z : ℂ) : 2 * (isqrt2 * (z * isqrt2)) = z := by
  linear_combination 2 * z * isqrt2_mul_isqrt2

@[simp] lemma conj_isqrt2 : (starRingEnd ℂ) isqrt2 = isqrt2 := by
  simp [isqrt2, ← Complex.ofReal_inv]

/-- The EPR pair `(|00⟩ + |11⟩)/√2` shared between Alice's second qubit and
Bob's qubit. -/
noncomputable def bellPair (j k : Fin 2) : ℂ := isqrt2 * (if j = k then 1 else 0)

/-- The Bell basis state `|β mn⟩ = (|0, n⟩ + (-1)^m |1, 1 ⊕ n⟩)/√2` in which
Alice measures her two qubits. -/
noncomputable def bellBasis (m n i j : Fin 2) : ℂ :=
  isqrt2 * (-1 : ℂ) ^ ((m : ℕ) * (i : ℕ)) * (if j = i + n then 1 else 0)

/-- The three–qubit input state `|ψ⟩ ⊗ |β₀₀⟩`: Alice's unknown qubit `ψ`
together with the shared EPR pair. -/
noncomputable def inputState (psi : Fin 2 → ℂ) (i j k : Fin 2) : ℂ :=
  psi i * bellPair j k

/-- Bob's (normalised) conditional state after Alice measures her two qubits in
the Bell basis and obtains the outcome `(m, n)`.  It is the projection of the
input state onto `|β mn⟩` on the first two tensor factors; the factor `2`
renormalises, since each outcome occurs with probability `1/4`. -/
noncomputable def postMeasurement (psi : Fin 2 → ℂ) (m n : Fin 2) (k : Fin 2) : ℂ :=
  2 * ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (bellBasis m n i j) * inputState psi i j k

/-- Bob's correction operator `Z^m X^n` applied to a one–qubit state. -/
noncomputable def correction (m n : Fin 2) (chi : Fin 2 → ℂ) (k : Fin 2) : ℂ :=
  (-1 : ℂ) ^ ((m : ℕ) * (k : ℕ)) * chi (k + n)

/-- Sanity check on the definitions: the four Bell states really do form an
orthonormal basis of the two–qubit space, so the Bell measurement above is a
genuine projective measurement. -/
lemma bellBasis_orthonormal (m n m' n' : Fin 2) :
    ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (bellBasis m n i j) * bellBasis m' n' i j
      = if m = m' ∧ n = n' then 1 else 0 := by
  fin_cases m <;> fin_cases n <;> fin_cases m' <;> fin_cases n' <;>
    simp [bellBasis, Fin.sum_univ_two] <;> ring

/-! ## The teleportation identity -/

/-- **Teleportation identity.**  For every one–qubit input state `ψ` and every
Bell-measurement outcome `(m, n)`, applying Bob's correction `Z^m X^n` to his
conditional post-measurement state returns exactly the input state `ψ`. -/
theorem teleportation_identity (psi : Fin 2 → ℂ) (m n : Fin 2) :
    correction m n (postMeasurement psi m n) = psi := by
  funext k
  fin_cases m <;> fin_cases n <;> fin_cases k <;>
    simp [correction, postMeasurement, inputState, bellBasis, bellPair,
      Fin.sum_univ_two] <;>
    exact two_mul_isqrt2_mul _

end QC

-- Axiom check for the target theorem.
#print axioms QC.teleportation_identity

