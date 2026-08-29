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

import RequestProject.QI.Basic

/-!
# The matrix geometric mean

For positive definite matrices `A`, `B` we define the geometric mean
`gmean A B = A^(1/2) (A^(-1/2) B A^(-1/2))^(1/2) A^(1/2)`, and prove:

* `gmean_block`: the block matrix `[[A, gmean A B], [gmean A B, B]]` is positive semidefinite;
* `gmean_max`: it is the largest hermitian `X` with `[[A, X], [X, B]] ⪰ 0`;
* `gmean_mono`: monotonicity in both arguments;
* `gmean_superadd`: superadditivity (equivalent to joint concavity);
* `gmean_of_commute`: `gmean A B = A^(1/2) B^(1/2)` when `A` and `B` commute.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The geometric mean of two positive definite matrices. -/

theorem self_le_abs {Y : Matrix n n ℂ} (hY : Y.IsHermitian) : Y ≤ CFC.abs Y := by
  have hsa : IsSelfAdjoint Y := hY
  have h := CFC.abs_sub_self Y hsa
  have h2 : (0 : Matrix n n ℂ) ≤ 2 • Y⁻ := by
    have := CFC.negPart_nonneg Y
    positivity
  rw [← sub_nonneg]
  rw [h]
  exact h2

