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

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma isUnit_P19 : IsUnit P19 := by
  refine IsUnit.of_mul_eq_one ((19 : ℂ)⁻¹ • Q19) ?_
  rw [Matrix.mul_smul, P19_mul_Q19, smul_smul]
  norm_num

/-- The explicit Hückel molecular orbitals: the vector `j ↦ ζ^(jk)` (with `ζ = exp (2πi/19)`)
is an eigenvector of the adjacency matrix of `C₁₉` with eigenvalue `2 cos (2πk/19)`. -/
