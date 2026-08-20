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

lemma trace_hermFun (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hermFun A hA f).trace = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hermFun, trace_conjStarAlgAut, Matrix.trace_diagonal]
  push_cast
  rfl

/-! ## Von Neumann entropy -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, defined spectrally as
`-∑ᵢ λᵢ log λᵢ`, with the usual convention `0 log 0 = 0` (which is automatic in Mathlib since
`Real.log 0 = 0`).  For non-Hermitian matrices the value is set to `0`. -/
