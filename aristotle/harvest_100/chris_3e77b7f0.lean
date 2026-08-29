/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- Computational basis states of 4 qubits, indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 := Fin 4 → Fin 2

/-- The all-zeros bit string `|0000⟩`. -/
def allZero : Qubits4 := fun _ => 0

/-- The all-ones bit string `|1111⟩`. -/
def allOne : Qubits4 := fun _ => 1

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector in the
16-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 4 → Fin 2)`. -/
noncomputable def ghz4 : EuclideanSpace ℂ Qubits4 :=
  WithLp.toLp 2 (fun i => if i = allZero ∨ i = allOne then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

lemma allZero_ne_allOne : allZero ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

lemma ghz4_apply_sq (i : Qubits4) :
    ‖ghz4 i‖ ^ 2 = if i ∈ ({allZero, allOne} : Finset Qubits4) then (1 / 2 : ℝ) else 0 := by
  by_cases h : i = allZero ∨ i = allOne
  · have hmem : i ∈ ({allZero, allOne} : Finset Qubits4) := by
      simpa [Finset.mem_insert] using h
    rw [if_pos hmem]
    simp only [ghz4, WithLp.ofLp_toLp, if_pos h, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), div_pow, one_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · have hmem : i ∉ ({allZero, allOne} : Finset Qubits4) := by
      simpa [Finset.mem_insert] using h
    rw [if_neg hmem]
    simp only [ghz4, WithLp.ofLp_toLp, if_neg h, norm_zero]
    norm_num

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Qubits4, ‖ghz4.ofLp i‖ ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun i _ => ghz4_apply_sq i)]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_pair allZero_ne_allOne]
    norm_num
  rw [hsum, Real.sqrt_one]

/-- The defining description of the GHZ state: it is `(|0000⟩ + |1111⟩)/√2`, where
`|b⟩` denotes the computational basis vector `EuclideanSpace.single b 1`. -/
theorem ghz4_eq_superposition :
    ghz4 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single allZero (1 : ℂ) + EuclideanSpace.single allOne (1 : ℂ)) := by
  ext i
  by_cases h0 : i = allZero
  · subst h0
    simp [ghz4, EuclideanSpace.single_apply, allZero_ne_allOne]
  · by_cases h1 : i = allOne
    · subst h1
      simp [ghz4, EuclideanSpace.single_apply, h0]
    · simp [ghz4, EuclideanSpace.single_apply, h0, h1]

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

