/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Bit flip on a single (qu)bit index. -/
def flip (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0

@[simp] lemma flip_zero : flip 0 = 1 := rfl
@[simp] lemma flip_one : flip 1 = 0 := rfl

/-- The maximally entangled pair `(|00⟩ + |11⟩)/√2` shared by Alice and Bob. -/
noncomputable def bell (b c : Fin 2) : ℂ :=
  if b = c then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

/-- The Bell basis state `|β i j⟩ = (|0, j⟩ + (-1)^i |1, flip j⟩)/√2`, in which Alice
measures her two qubits. -/
noncomputable def bellBasis (i j : Fin 2) (a b : Fin 2) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
    ((if a = 0 ∧ b = j then 1 else 0) +
      (-1) ^ (i : ℕ) * (if a = 1 ∧ b = flip j then 1 else 0))

/-- The three-qubit input state `|ψ⟩ ⊗ |Φ⁺⟩`: qubit `a` is the unknown state to be
teleported, qubits `b, c` are the entangled pair. -/
noncomputable def initialState (psi : Fin 2 → ℂ) (a b c : Fin 2) : ℂ :=
  psi a * bell b c

/-- Bob's (normalized) qubit after Alice's Bell measurement yields outcome `(i, j)`.
It is obtained by projecting the input state onto `|β i j⟩` on Alice's two qubits and
rescaling by the factor `2 = 1/√(1/4)` coming from the outcome probability `1/4`. -/
noncomputable def postMeasure (psi : Fin 2 → ℂ) (i j : Fin 2) (c : Fin 2) : ℂ :=
  2 * ∑ a : Fin 2, ∑ b : Fin 2, star (bellBasis i j a b) * initialState psi a b c

/-- The Pauli `X` gate. -/
def applyX (v : Fin 2 → ℂ) : Fin 2 → ℂ := fun c => v (flip c)

/-- The Pauli `Z` gate. -/
def applyZ (v : Fin 2 → ℂ) : Fin 2 → ℂ := fun c => (if c = 0 then 1 else -1) * v c

/-- Bob's correction for the classical outcome `(i, j)`: apply `X^j` and then `Z^i`. -/
noncomputable def correct (i j : Fin 2) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  applyZ^[(i : ℕ)] (applyX^[(j : ℕ)] v)

private lemma sqrt_two_inv_sq : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    = (2 : ℂ)⁻¹ := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [← mul_inv, h]

/-- **Quantum teleportation identity.**  For every input qubit state `ψ` and every
Bell-measurement outcome `(i, j)`, Bob's qubit after applying the correction `Z^i X^j`
is exactly the input state `ψ`. -/
theorem teleportation_identity (psi : Fin 2 → ℂ) (i j : Fin 2) :
    correct i j (postMeasure psi i j) = psi := by
  funext c
  fin_cases i <;> fin_cases j <;> fin_cases c <;>
    simp [correct, postMeasure, initialState, bellBasis, bell, applyX, applyZ,
      Fin.sum_univ_succ, Complex.ext_iff] <;>
    ring_nf <;>
    simp [Real.sq_sqrt] <;>
    ring_nf <;>
    trivial

/-- Sanity check: the correction is genuinely needed — for the outcome `(1, 0)` the
uncorrected state of Bob's qubit is not the input state in general. -/
theorem postMeasure_ne_of_no_correction :
    ∃ psi : Fin 2 → ℂ, postMeasure psi 1 0 ≠ psi := by
  refine ⟨![0, 1], fun h => ?_⟩
  have h1 := congrFun h 1
  simp [postMeasure, initialState, bellBasis, bell, Fin.sum_univ_succ] at h1
  rw [sqrt_two_inv_sq] at h1
  norm_num at h1

end QC

