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

lemma sum_conj_mul_of_norm (psi : n → ℂ) (h : ∑ i, ‖psi i‖ ^ 2 = 1) :
    ∑ i, (starRingEnd ℂ) (psi i) * psi i = 1 := by
  have key : ∀ i : n, (starRingEnd ℂ) (psi i) * psi i = ((‖psi i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Complex.ofReal_sum, h, Complex.ofReal_one]

omit [DecidableEq n] in
/-- A normalised pure state has unit trace, i.e. it is a density matrix. -/
