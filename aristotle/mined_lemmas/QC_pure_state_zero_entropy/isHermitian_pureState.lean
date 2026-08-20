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

open scoped Matrix

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed
spectrally: since `ρ` is Hermitian it is unitarily diagonalizable with real eigenvalues
`λ i`, and `-Tr(ρ log ρ) = -∑ i, λ i * log (λ i)`.  (As usual `0 * log 0 = 0`, which is
automatic with Mathlib's convention `Real.log 0 = 0`.) -/

theorem isHermitian_pureState (psi : n → ℂ) : (pureState psi).IsHermitian := by
  ext i j
  simp [pureState, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

omit [DecidableEq n] in
/-- A normalized vector gives a density matrix of unit trace. -/
