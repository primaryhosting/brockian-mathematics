/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The trace norm (Schatten `1`-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/

lemma trace_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self]
  rw [one_mul, Matrix.trace_diagonal]
  push_cast
  simp [Function.comp_def]

/-- The trace of `cos (t • A)` for a Hermitian matrix `A` is real, equal to the sum of
`cos (t * λ)` over the eigenvalues `λ` of `A`. -/
