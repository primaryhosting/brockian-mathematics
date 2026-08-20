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

theorem vonNeumannEntropy_eq_sum {ρ : Matrix n n ℂ} (h : ρ.IsHermitian) :
    vonNeumannEntropy h =
      -∑ i, ((h.eigenvalues i * Real.log (h.eigenvalues i) : ℝ) : ℂ) := by
  have hprod : ρ * hermLog h =
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary
        (Matrix.diagonal fun i => ((h.eigenvalues i * Real.log (h.eigenvalues i) : ℝ) : ℂ)) := by
    conv_lhs => rw [h.spectral_theorem]
    rw [hermLog, ← map_mul]
    congr 1
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    push_cast
    rfl
  rw [vonNeumannEntropy, hprod, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]

/-- **The von Neumann entropy of a pure state is zero.** -/
