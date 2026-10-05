import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 4-qubit system is indexed by bit strings `Fin 4 → Bool`. -/
abbrev Qubits4 := Fin 4 → Bool

/-- The all-zeros bit string, i.e. the basis label of `|0000⟩`. -/
def allZero : Qubits4 := fun _ => false

/-- The all-ones bit string, i.e. the basis label of `|1111⟩`. -/
def allOne : Qubits4 := fun _ => true

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector of the
Hilbert space `EuclideanSpace ℂ (Fin 4 → Bool)`. -/
noncomputable def ghz4 : EuclideanSpace ℂ Qubits4 :=
  WithLp.toLp 2 fun x => if x = allZero ∨ x = allOne then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

lemma allZero_ne_allOne : (allZero : Qubits4) ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- `ghz4` is indeed `(1/√2) • (|0000⟩ + |1111⟩)`, where `|b⟩` denotes the standard basis
vector `EuclideanSpace.single b 1`. -/
lemma ghz4_eq_smul_add_single :
    ghz4 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single allZero (1 : ℂ) + EuclideanSpace.single allOne (1 : ℂ)) := by
  ext x
  by_cases h0 : x = allZero <;> by_cases h1 : x = allOne <;>
    simp [ghz4, EuclideanSpace.single_apply, h0, h1, allZero_ne_allOne, allZero_ne_allOne.symm]

lemma ghz4_allZero : ghz4.ofLp allZero = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [ghz4]

lemma ghz4_allOne : ghz4.ofLp allOne = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [ghz4]

lemma ghz4_eq_zero {x : Qubits4} (h0 : x ≠ allZero) (h1 : x ≠ allOne) : ghz4.ofLp x = 0 := by
  simp [ghz4, h0, h1]

lemma sq_norm_coeff : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), div_pow, one_pow,
    Real.sq_sqrt (by norm_num)]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ x : Qubits4, ‖ghz4.ofLp x‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_add_of_mem allZero allOne (Finset.mem_univ _) (Finset.mem_univ _)
      allZero_ne_allOne ?_]
    · rw [ghz4_allZero, ghz4_allOne, sq_norm_coeff]
      norm_num
    · rintro c - ⟨h0, h1⟩
      rw [ghz4_eq_zero h0 h1]
      simp
  rw [hsum, Real.sqrt_one]

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

