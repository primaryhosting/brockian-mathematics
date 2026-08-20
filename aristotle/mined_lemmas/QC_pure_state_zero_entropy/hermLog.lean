/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The logarithm of a Hermitian matrix, defined through its spectral decomposition:
if `ρ = U D U*` with `D` the diagonal matrix of eigenvalues, then
`log ρ = U (log D) U*`. -/

noncomputable def hermLog {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary
    (Matrix.diagonal fun i => ((Real.log (h.eigenvalues i) : ℝ) : ℂ))

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`. -/
