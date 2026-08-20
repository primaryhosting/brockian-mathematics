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

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma eigen_sqrt_two :
    ∃ v : Fin 8 → ℝ, v ≠ 0 ∧ C8adj *ᵥ v = (Real.sqrt 2) • v := by
  refine ⟨![Real.sqrt 2, 1, 0, -1, -Real.sqrt 2, -1, 0, 1],
    vec_ne_zero_of_head sqrt_two_ne_zero, ?_⟩
  rw [C8adj_mulVec_cons]
  funext i
  have h2 := sqrt_two_sq
  fin_cases i <;> simp <;> nlinarith [h2]

