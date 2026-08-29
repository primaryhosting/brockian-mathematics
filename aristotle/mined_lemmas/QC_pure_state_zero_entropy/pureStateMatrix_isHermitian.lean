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

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed in the
eigenbasis: `S(ρ) = ∑ i, -λ i * log (λ i)` where the `λ i` are the (real) eigenvalues of `ρ`.
This is the standard definition of the entropy of a density matrix. -/

theorem pureStateMatrix_isHermitian (psi : n → ℂ) :
    (pureStateMatrix psi).IsHermitian := by
  ext i j
  simp [pureStateMatrix, Matrix.conjTranspose_apply, mul_comm]

omit [DecidableEq n] in
/-- For a unit vector `ψ`, the pure-state density matrix `|ψ⟩⟨ψ|` is idempotent
(it is an orthogonal projection onto the line spanned by `ψ`). -/
