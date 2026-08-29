/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of `n` qubits, realized as the Hilbert space `ℂ^(2^n)` with
basis vectors indexed by bit strings `Fin n → Fin 2`. -/
abbrev QubitState (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

/-- The all-zeros bit string `0…0`, indexing the basis vector `|0…0⟩`. -/
def allZeros (n : ℕ) : Fin n → Fin 2 := fun _ => 0

/-- The all-ones bit string `1…1`, indexing the basis vector `|1…1⟩`. -/
def allOnes (n : ℕ) : Fin n → Fin 2 := fun _ => 1

/-- The `n`-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
noncomputable def ghz (n : ℕ) : QubitState n :=
  ((Real.sqrt 2 : ℂ))⁻¹ •
    (EuclideanSpace.single (allZeros n) 1 + EuclideanSpace.single (allOnes n) 1)

/-- For at least one qubit, the all-zeros and all-ones bit strings are distinct. -/
theorem allZeros_ne_allOnes {n : ℕ} (hn : 0 < n) : allZeros n ≠ allOnes n := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp [allZeros, allOnes] at this

/-- The norm of the unnormalized superposition `|0…0⟩ + |1…1⟩` is `√2`. -/
theorem norm_zeros_add_ones {n : ℕ} (hn : 0 < n) :
    ‖(EuclideanSpace.single (allZeros n) (1 : ℂ) +
      EuclideanSpace.single (allOnes n) 1)‖ = Real.sqrt 2 := by
  have hne : allZeros n ≠ allOnes n := allZeros_ne_allOnes hn
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Finset.sum_congr rfl
    (g := fun x => (if x = allZeros n then (1 : ℝ) else 0) +
      (if x = allOnes n then 1 else 0))]
  · rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    norm_num
  · intro x _
    by_cases hx : x = allZeros n <;> by_cases hy : x = allOnes n <;>
      simp_all [EuclideanSpace.single_apply]

/-- The `n`-qubit GHZ state is a unit vector, for every `n ≥ 1`. -/
theorem ghz_normalized {n : ℕ} (hn : 0 < n) : ‖ghz n‖ = 1 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [ghz, norm_smul, norm_zeros_add_ones hn]
  simp only [Complex.norm_real, norm_inv]
  rw [Real.norm_eq_abs, abs_of_pos h2, inv_mul_cancel₀ h2.ne']

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz7_normalized : ‖ghz 7‖ = 1 := ghz_normalized (by norm_num)

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

