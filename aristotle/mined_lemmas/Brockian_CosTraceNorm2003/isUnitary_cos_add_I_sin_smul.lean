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

/-!
# The `CosTraceNorm` family: trace-norm bounds for Hermitian matrices

For a Hermitian matrix `A` the *trace norm* (Schatten 1-norm) `‖A‖₁` is the sum of the absolute
values of its eigenvalues.  This file develops a small family of bounds for it:

* `Brockian.CosTraceNorm2001` : `|Tr A| ≤ ‖A‖₁`;
* `Brockian.CosTraceNorm2002` : the dual (Hölder-type) bound `|Tr (A U)| ≤ ‖A‖₁` for `U` unitary;
* `Brockian.CosTraceNorm2003` : a new cosine-parametrised bound.  If `B` is a Hermitian unitary
  (a reflection), then for every angle `t`,
  `√((cos t · Tr A)² + (sin t · Tr (A B))²) ≤ ‖A‖₁`,
  i.e. the point `(Tr A, Tr (A B))` lies inside every ellipse `x²/sec²t + y²/csc²t = ‖A‖₁²`.
-/

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **trace norm** (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute values
of its eigenvalues. -/

lemma isUnitary_cos_add_I_sin_smul {B : Matrix n n ℂ} (hB : B.IsHermitian) (hB2 : B * B = 1)
    (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ((c : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (s : ℂ)) • B)ᴴ *
      ((c : ℂ) • (1 : Matrix n n ℂ) + (Complex.I * (s : ℂ)) • B) = 1 := by
  have hBH : Bᴴ = B := hB.eq
  have key : ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hBH, Matrix.conjTranspose_one,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hB2, star_mul', Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal, smul_add, smul_smul]
  match_scalars
  · linear_combination key - ((s : ℂ) ^ 2) * Complex.I_sq
  · ring

/-- `CosTraceNorm2003`: a cosine-parametrised trace-norm bound.  If `A` is Hermitian and `B` is a
Hermitian unitary (a reflection: `Bᴴ = B` and `B * B = 1`), then for every angle `t` the point
`(cos t · Tr A, sin t · Tr (A B))` lies in the disc of radius `‖A‖₁`. -/
