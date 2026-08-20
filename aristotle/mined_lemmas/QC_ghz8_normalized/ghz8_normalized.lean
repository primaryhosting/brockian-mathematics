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

/-- The state space of 8 qubits: the (finite-dimensional) complex Hilbert space with orthonormal
basis indexed by bit strings `Fin 8 → Bool`. -/
abbrev Qubits8 : Type := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The computational basis state `|x⟩` for a bit string `x : Fin 8 → Bool`. -/

theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  have hne := allFalse_ne_allTrue
  rw [EuclideanSpace.norm_eq]
  have key : ∀ x : Fin 8 → Bool, ‖ghz8 x‖ ^ 2 =
      (if x = (fun _ => false) then (1 / 2 : ℝ) else 0)
        + (if x = (fun _ => true) then (1 / 2 : ℝ) else 0) := by
    intro x
    rw [ghz8_apply]
    by_cases h1 : x = (fun _ => false)
    · subst h1; simp [hne]
    · by_cases h2 : x = (fun _ => true)
      · subst h2; simp [h1]
      · simp [h1, h2]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.sum_ite_eq' Finset.univ]
  norm_num

end QC

