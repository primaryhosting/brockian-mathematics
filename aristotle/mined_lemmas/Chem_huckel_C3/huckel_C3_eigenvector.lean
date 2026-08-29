/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃` (every pair of distinct vertices
is adjacent). In Hückel theory this is the (shifted, scaled) Hamiltonian of the
cyclic three-carbon π-system. -/

theorem huckel_C3_eigenvector (k : Fin 3) :
    c3vec k ≠ 0 ∧
      C3adjC.mulVec (c3vec k)
        = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) : ℝ) : ℂ) • c3vec k := by
  refine ⟨c3vec_ne_zero k, ?_⟩
  have h4 : c3root ^ 4 = c3root := by
    calc c3root ^ 4 = c3root ^ 3 * c3root := by ring
      _ = c3root := by rw [c3root_pow_three]; ring
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.mulVec, Fin.sum_univ_three, C3adjC, c3vec, dotProduct, ccos_one, ccos_two,
      h4] <;>
    first
      | linear_combination c3root_sum
      | norm_num

end Chem

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

