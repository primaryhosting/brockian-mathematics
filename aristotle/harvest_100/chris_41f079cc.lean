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

/-- The computational-basis label of `|000000⟩`. -/
def allZeros : Fin 6 → Fin 2 := fun _ => 0

/-- The computational-basis label of `|111111⟩`. -/
def allOnes : Fin 6 → Fin 2 := fun _ => 1

theorem allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
Hilbert space `EuclideanSpace ℂ (Fin 6 → Fin 2)` of 6 qubits. -/
noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Fin 2) :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    (EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ))

/-- The amplitudes of the GHZ state: `1/√2` on the two all-equal basis states, `0` elsewhere. -/
theorem ghz6_apply (x : Fin 6 → Fin 2) :
    ghz6 x = if x = allZeros ∨ x = allOnes then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0 := by
  have hab : allZeros ≠ allOnes := allZeros_ne_allOnes
  by_cases h0 : x = allZeros
  · subst h0; simp [ghz6, EuclideanSpace.single_apply, hab]
  · by_cases h1 : x = allOnes
    · subst h1; simp [ghz6, EuclideanSpace.single_apply, Ne.symm hab]
    · simp [ghz6, EuclideanSpace.single_apply, h0, h1]

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2` is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have hab : allZeros ≠ allOnes := allZeros_ne_allOnes
  have key : ∀ x : Fin 6 → Fin 2, ‖ghz6 x‖ ^ 2 =
      (if x = allZeros then (1:ℝ)/2 else 0) + (if x = allOnes then (1:ℝ)/2 else 0) := by
    intro x
    rw [ghz6_apply]
    by_cases h0 : x = allZeros
    · subst h0; simp [hab]
    · by_cases h1 : x = allOnes
      · subst h1; simp [Ne.symm hab]
      · simp [h0, h1]
  rw [EuclideanSpace.norm_eq, Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ allZeros (fun _ => (1:ℝ)/2),
    Finset.sum_ite_eq' Finset.univ allOnes (fun _ => (1:ℝ)/2)]
  norm_num

end QC

