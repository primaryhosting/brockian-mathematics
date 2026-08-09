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

/-- The all-zeros bit string on 7 qubits, i.e. the label of the basis vector `|0…0⟩`. -/
def allZeros : Fin 7 → Fin 2 := fun _ => 0

/-- The all-ones bit string on 7 qubits, i.e. the label of the basis vector `|1…1⟩`. -/
def allOnes : Fin 7 → Fin 2 := fun _ => 1

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 7 → Fin 2)` (whose coordinates are indexed by 7-bit strings). -/
noncomputable def ghz7 : EuclideanSpace ℂ (Fin 7 → Fin 2) :=
  WithLp.toLp 2 (fun v => if v = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ) else
    if v = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

@[simp] theorem ghz7_apply (v : Fin 7 → Fin 2) :
    ghz7.ofLp v = if v = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ) else
      if v = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := rfl

theorem allZeros_ne_allOnes : (allZeros : Fin 7 → Fin 2) ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  have key : ∀ v : Fin 7 → Fin 2, ‖ghz7.ofLp v‖ ^ 2
      = (if v = allZeros then (1 / 2 : ℝ) else 0) + (if v = allOnes then (1 / 2 : ℝ) else 0) := by
    intro v
    have hs : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow, one_pow,
        Real.sq_sqrt (by norm_num)]
    by_cases h0 : v = allZeros
    · subst h0
      rw [ghz7_apply, if_pos rfl, if_pos rfl, if_neg allZeros_ne_allOnes, hs, add_zero]
    · by_cases h1 : v = allOnes
      · subst h1
        rw [ghz7_apply, if_neg h0, if_pos rfl, if_neg h0, if_pos rfl, hs, zero_add]
      · simp [h0, h1]
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ v : Fin 7 → Fin 2, ‖ghz7.ofLp v‖ ^ 2 = 1 := by
    simp only [key]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ allZeros (fun _ => (1 / 2 : ℝ)),
      Finset.sum_ite_eq' Finset.univ allOnes (fun _ => (1 / 2 : ℝ))]
    norm_num
  rw [hsum, Real.sqrt_one]

end QC
#print axioms QC.ghz7_normalized

