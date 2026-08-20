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

open scoped Real

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Chem

/-- Adjacency matrix of the cycle graph `C₆` (the Hückel connectivity matrix of benzene):
vertex `i` is adjacent to `i ± 1 mod 6`. -/

lemma C6sq_mul_self :
    C6sq * C6sq = (5 : ℂ) • C6sq - (4 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [C6sq, Matrix.mul_apply, Fin.sum_univ_six, Matrix.of_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      norm_num

/-- If `v ≠ 0` is an eigenvector of the adjacency matrix with eigenvalue `μ`, then
`μ⁴ - 5μ² + 4 = 0`, i.e. `μ ∈ {2, 1, -1, -2}`. -/
