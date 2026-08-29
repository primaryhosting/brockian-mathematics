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

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₆`,
i.e. of the benzene carbon skeleton. -/

theorem C6adj_has_eigenvector (mu : ℂ) (h : mu = 2 ∨ mu = 1 ∨ mu = -1 ∨ mu = -2) :
    ∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6adj.mulVec v = mu • v := by
  rcases h with rfl | rfl | rfl | rfl
  · refine ⟨![1,1,1,1,1,1], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num
  · refine ⟨![1,1,0,-1,-1,0], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · refine ⟨![1,-1,0,1,-1,0], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · refine ⟨![1,-1,1,-1,1,-1], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

/-- Any eigenvalue of the `C₆` adjacency matrix is one of `2, 1, -1, -2`. -/
