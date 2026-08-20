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

namespace QPhys

open Matrix

/-- The columns of a matrix `U` with `Uᴴ * U = 1` are nonzero. -/

private lemma col_ne_zero_of_conjTranspose_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {𝕜 : Type*} [RCLike 𝕜] {U : Matrix n n 𝕜} (h : Uᴴ * U = 1) (j : n) :
    (fun i => U i j) ≠ 0 := by
  intro hz
  have hjj := congrFun (congrFun h j) j
  rw [Matrix.mul_apply] at hjj
  have hz' : ∀ i, U i j = 0 := fun i => congrFun hz i
  simp [hz'] at hjj

/-- **Spectral theorem for Hermitian matrices** (finite dimensions).

Every Hermitian matrix `A` over an `RCLike` field `𝕜` (e.g. `ℝ` or `ℂ`) is unitarily
diagonalizable with *real* eigenvalues: there is a unitary matrix `U` (i.e. `Uᴴ * U = 1`
and `U * Uᴴ = 1`) and a family of **real** numbers `d : n → ℝ` such that

* `A = U * diagonal (d) * Uᴴ`, equivalently `Uᴴ * A * U = diagonal (d)`, and
* the `j`-th column of `U` is a nonzero eigenvector of `A` with eigenvalue `d j`.

Thus the columns of `U` form an orthonormal eigenbasis and all eigenvalues are real. -/
