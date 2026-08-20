/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis states of a 5-qubit register are indexed by `Fin 5 → Bool`. -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros bit string `|00000⟩`. -/
def allZeros : Qubits5 := fun _ => false

/-- The all-ones bit string `|11111⟩`. -/
def allOnes : Qubits5 := fun _ => true

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(2^5)` indexed by bit strings. -/
noncomputable def ghz5 : EuclideanSpace ℂ Qubits5 :=
  WithLp.toLp 2 (fun x =>
    if x = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if x = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0)

theorem allZeros_ne_allOnes : (allZeros : Qubits5) ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

theorem ghz5_apply (x : Qubits5) :
    ghz5.ofLp x =
      if x = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else if x = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else 0 := rfl

theorem norm_sq_coeff (x : Qubits5) :
    ‖ghz5.ofLp x‖ ^ 2 = (if x = allZeros then (1 / 2 : ℝ) else 0)
      + (if x = allOnes then (1 / 2 : ℝ) else 0) := by
  have habs : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.sqrt 2), div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [ghz5_apply]
  by_cases h0 : x = allZeros
  · subst h0
    rw [if_pos rfl, if_pos rfl, if_neg allZeros_ne_allOnes, habs]
    norm_num
  · by_cases h1 : x = allOnes
    · subst h1
      rw [if_neg h0, if_pos rfl, if_neg h0, if_pos rfl, habs]
      norm_num
    · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
      norm_num

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2` is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ x : Qubits5, ‖ghz5.ofLp x‖ ^ 2 = 1 := by
    simp only [norm_sq_coeff, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
    norm_num
  rw [h, Real.sqrt_one]

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

