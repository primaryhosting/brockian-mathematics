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

/-
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Matrix

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed in the
eigenbasis: if `ρ = U diag(λ) U*` then `-Tr(ρ log ρ) = -∑ λ i * log (λ i)`, i.e. the sum of
`Real.negMulLog` over the eigenvalues. -/

noncomputable def matrixLog {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : Matrix n n ℂ :=
  (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ)) *
    star (hρ.eigenvectorUnitary : Matrix n n ℂ)

/-- The eigenvalue formula for the entropy really does compute `-Tr(ρ log ρ)`. -/
