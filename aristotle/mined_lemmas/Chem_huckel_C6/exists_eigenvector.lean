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

/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open SimpleGraph Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆`, over `ℂ`
(the Hückel matrix of benzene in units where `α = 0`, `β = 1`). -/

lemma exists_eigenvector (k : ℕ) (hk : k < 6) :
    ∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6 *ᵥ v = ((lam k : ℝ) : ℂ) • v := by
  interval_cases k
  · rw [lam_zero]
    push_cast
    refine eigen_of ![1,1,1,1,1,1] 2 (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  · rw [lam_one]
    push_cast
    refine eigen_of ![1,1,0,-1,-1,0] 1 (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · rw [lam_two]
    push_cast
    refine eigen_of ![1,-1,0,1,-1,0] (-1) (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · rw [lam_three]
    push_cast
    refine eigen_of ![1,-1,1,-1,1,-1] (-2) (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring
  · rw [lam_four]
    push_cast
    refine eigen_of ![1,-1,0,1,-1,0] (-1) (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · rw [lam_five]
    push_cast
    refine eigen_of ![1,1,0,-1,-1,0] 1 (by norm_num) ?_
    ext i
    fin_cases i <;>
      simp [C6_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

/-- The adjacency matrix of `C₆` satisfies `A⁴ = 5A² - 4I`. -/
