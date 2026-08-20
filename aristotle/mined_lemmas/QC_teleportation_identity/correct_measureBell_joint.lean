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

