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

namespace QC

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Functional calculus for Hermitian matrices

Given a Hermitian matrix `A` with unitary diagonalization `A = U D Uᴴ`, and a real function `f`,
`QC.hermFun A hA f` is the matrix `U f(D) Uᴴ`.  This is the usual (Borel/continuous) functional
calculus in finite dimensions; it lets us give a literal meaning to expressions such as
`ρ log ρ`. -/

/-- Functional calculus: `f` applied to the Hermitian matrix `A` through its spectral
decomposition. -/

lemma eigenvalues_sq_eq_self_of_idempotent {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : A * A = A) (i : n) : hA.eigenvalues i * hA.eigenvalues i = hA.eigenvalues i := by
  set f := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) (star hA.eigenvectorUnitary) with hf
  have h1 : f A = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have h2 : f A * f A = f A := by rw [← map_mul, h]
  rw [h1, Matrix.diagonal_mul_diagonal] at h2
  have h3 := congrFun (congrFun h2 i) i
  simp only [Matrix.diagonal_apply_eq, Function.comp_apply] at h3
  exact_mod_cast h3

/-- Each eigenvalue of an idempotent Hermitian matrix is `0` or `1`. -/
