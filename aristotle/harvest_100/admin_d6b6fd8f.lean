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

namespace QC

/-- A qubit state: a vector of amplitudes indexed by the computational basis `{0,1}`. -/
abbrev Qubit := Fin 2 → ℂ

/-- The Pauli `X` (bit flip) gate. -/
def pauliX (v : Qubit) : Qubit := fun c => v (c + 1)

/-- The Pauli `Z` (phase flip) gate. -/
def pauliZ (v : Qubit) : Qubit := fun c => (-1 : ℂ) ^ (c : ℕ) * v c

/-- `pauliXp j` is `X ^ j` for `j : Fin 2`. -/
def pauliXp (j : Fin 2) (v : Qubit) : Qubit := fun c => v (c + j)

/-- `pauliZp i` is `Z ^ i` for `i : Fin 2`. -/
def pauliZp (i : Fin 2) (v : Qubit) : Qubit := fun c => (-1 : ℂ) ^ ((i : ℕ) * (c : ℕ)) * v c

/-- The four Bell states, written as `2 × 2` amplitude arrays:
`bell i j = (Z ^ i X ^ j ⊗ I) |Φ⁺⟩` where `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`.
In particular `bell 0 0` is `|Φ⁺⟩` itself. -/
noncomputable def bell (i j : Fin 2) (a b : Fin 2) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if a = b + j then (-1 : ℂ) ^ ((i : ℕ) * (a : ℕ)) else 0)

/-- The three-qubit input state of the protocol: the unknown qubit `psi` (register 1)
tensored with a Bell pair `|Φ⁺⟩` shared between registers 2 and 3. -/
noncomputable def joint (psi : Qubit) (a b c : Fin 2) : ℂ := psi a * bell 0 0 b c

/-- The (unnormalized) state left in register 3 when a Bell measurement on registers 1
and 2 yields the outcome `(i, j)`, i.e. the partial inner product of the joint state
with the Bell state `bell i j`. -/
noncomputable def measureBell (i j : Fin 2) (T : Fin 2 → Fin 2 → Fin 2 → ℂ) : Qubit :=
  fun c => ∑ a : Fin 2, ∑ b : Fin 2, (starRingEnd ℂ) (bell i j a b) * T a b c

/-- The correction unitary `Z ^ i X ^ j` applied by the receiver on outcome `(i, j)`. -/
noncomputable def correct (i j : Fin 2) (v : Qubit) : Qubit := pauliZp i (pauliXp j v)

/-- The Euclidean norm of a qubit state. -/
noncomputable def nrm (v : Qubit) : ℝ := Real.sqrt (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2)

/-- Normalization of a (nonzero) qubit state. -/
noncomputable def normalize (v : Qubit) : Qubit := fun c => ((nrm v : ℝ) : ℂ)⁻¹ * v c

lemma inv_sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [inv_pow, h]
  norm_num

@[simp] lemma pauliXp_zero : pauliXp 0 = id := by
  funext v c; simp [pauliXp]

@[simp] lemma pauliXp_one : pauliXp 1 = pauliX := by
  funext v c; simp [pauliXp, pauliX]

@[simp] lemma pauliZp_zero : pauliZp 0 = id := by
  funext v c; simp [pauliZp]

@[simp] lemma pauliZp_one : pauliZp 1 = pauliZ := by
  funext v c; simp [pauliZp, pauliZ]

/-- The four Bell states form an orthonormal basis of the two-qubit space, so measuring in
this basis is a genuine projective measurement. -/
lemma bell_orthonormal (i j i' j' : Fin 2) :
    (∑ a : Fin 2, ∑ b : Fin 2, (starRingEnd ℂ) (bell i j a b) * bell i' j' a b)
      = if i = i' ∧ j = j' then 1 else 0 := by
  have h11 : (1 + 1 : Fin 2) = 0 := rfl
  simp only [bell, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    norm_num [h11] <;> ring_nf <;> rw [inv_sqrt_two_sq] <;> ring

/-- After a Bell measurement with outcome `(i, j)`, register 3 holds `(1/2) • X ^ j Z ^ i |ψ⟩`. -/
lemma measureBell_joint (psi : Qubit) (i j : Fin 2) :
    measureBell i j (joint psi) = fun c => (1 / 2 : ℂ) * pauliXp j (pauliZp i psi) c := by
  have h11 : (1 + 1 : Fin 2) = 0 := rfl
  funext c
  simp only [measureBell, joint, bell, pauliXp, pauliZp, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases c <;>
    norm_num [h11] <;> ring_nf <;> rw [inv_sqrt_two_sq] <;> ring

/-- The corrected state of register 3 is exactly `(1/2) • |ψ⟩`. -/
lemma correct_measureBell_joint (psi : Qubit) (i j : Fin 2) :
    correct i j (measureBell i j (joint psi)) = fun c => (1 / 2 : ℂ) * psi c := by
  funext c
  rw [correct, measureBell_joint]
  simp only [pauliXp, pauliZp]
  have h1 : ((-1 : ℂ) ^ ((i : ℕ) * (c : ℕ))) * ((-1 : ℂ) ^ ((i : ℕ) * ((c + j + j : Fin 2) : ℕ)))
      = 1 := by
    have : (c + j + j : Fin 2) = c := by fin_cases j <;> fin_cases c <;> rfl
    rw [this, ← pow_add, ← two_mul, pow_mul]
    norm_num
  have h2 : (c + j + j : Fin 2) = c := by fin_cases j <;> fin_cases c <;> rfl
  calc (-1 : ℂ) ^ ((i : ℕ) * (c : ℕ)) *
        (1 / 2 * ((-1 : ℂ) ^ ((i : ℕ) * ((c + j + j : Fin 2) : ℕ)) * psi (c + j + j)))
      = ((-1 : ℂ) ^ ((i : ℕ) * (c : ℕ)) * (-1 : ℂ) ^ ((i : ℕ) * ((c + j + j : Fin 2) : ℕ)))
          * (1 / 2 * psi (c + j + j)) := by ring
    _ = 1 / 2 * psi c := by rw [h1, h2]; ring

lemma nrm_smul_half (psi : Qubit) (hpsi : nrm psi = 1) :
    nrm (fun c => (1 / 2 : ℂ) * psi c) = 1 / 2 := by
  have h : ‖psi 0‖ ^ 2 + ‖psi 1‖ ^ 2 = 1 := by
    have := hpsi
    rw [nrm] at this
    have hnn : (0:ℝ) ≤ ‖psi 0‖ ^ 2 + ‖psi 1‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnn, this]
  rw [nrm]
  have e : ‖(1 / 2 : ℂ) * psi 0‖ ^ 2 + ‖(1 / 2 : ℂ) * psi 1‖ ^ 2 = (1 / 2) ^ 2 := by
    rw [norm_mul, norm_mul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    nlinarith [h]
  rw [e, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]

/-- **Quantum teleportation.** For any qubit state `|ψ⟩` of unit norm and any Bell-measurement
outcome `(i, j)`, the state of the receiver's qubit after applying the correction `Z ^ i X ^ j`
(and renormalizing) is exactly the input state `|ψ⟩`. -/
theorem teleportation_identity (psi : Qubit) (hpsi : nrm psi = 1) (i j : Fin 2) :
    normalize (correct i j (measureBell i j (joint psi))) = psi := by
  rw [correct_measureBell_joint]
  funext c
  rw [normalize, nrm_smul_half psi hpsi]
  push_cast
  field_simp

end QC

