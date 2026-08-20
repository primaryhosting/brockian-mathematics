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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ## The adjacency matrix of the cycle graph `C₉` -/

/-- The adjacency matrix of the cycle graph `C₉`, i.e. the Hückel matrix of the
cyclononatetraenyl π-system with `α = 0` and `β = 1`. -/

lemma pow_shift_identity {z : ℂ} (hz9 : z ^ 9 = 1) (i : Fin 9) :
    z ^ ((i + 1 : Fin 9) : ℕ) + z ^ ((i - 1 : Fin 9) : ℕ) = z ^ (i : ℕ) * (z + z⁻¹) := by
  have hz : z ≠ 0 := by
    intro h
    rw [h] at hz9
    simp at hz9
  have hinv : z⁻¹ = z ^ 8 := by
    field_simp
    linear_combination -hz9
  rw [hinv]
  fin_cases i <;> simp
  · linear_combination -hz9
  · linear_combination -z * hz9
  · linear_combination -z ^ 2 * hz9
  · linear_combination -z ^ 3 * hz9
  · linear_combination -z ^ 4 * hz9
  · linear_combination -z ^ 5 * hz9
  · linear_combination -z ^ 6 * hz9
  · linear_combination -(1 + z ^ 7) * hz9

/-! ## Diagonalisation over `ℂ` -/

/-- The complexified adjacency matrix. -/
