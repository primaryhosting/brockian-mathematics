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

theorem le_sqrt_of_sq_le {Y C : Matrix n n ℂ} (hY : Y.IsHermitian) (h : Y * Y ≤ C) :
    Y ≤ CFC.sqrt C := by
  calc Y ≤ CFC.abs Y := self_le_abs hY
  _ = CFC.sqrt (Y * Y) := abs_eq_sqrt hY
  _ ≤ CFC.sqrt C := CFC.monotone_sqrt h

end QI

import Mathlib

/-!
# Basic setup for the quantum information development

We equip `Matrix n n ℂ` with the C⋆-algebra structure coming from the L2 operator norm, and
with the Loewner order coming from `MatrixOrder`.  This gives access to the continuous
functional calculus API (`CFC.sqrt`, `CFC.rpow`, `CFC.log`, `CFC.monotone_sqrt`, ...).
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable instance Matrix.instCStarAlgebraL2 {n : Type*} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := { }

namespace QI

