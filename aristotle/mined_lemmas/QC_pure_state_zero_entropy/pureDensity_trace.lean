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
-- (The required header is kept verbatim above; Lean forbids a module docstring `/-!`
-- before `import`, so it is written as an ordinary block comment.)

import Mathlib

open Matrix Finset

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The density matrix `ρ = |ψ⟩⟨ψ|` of the (column) vector `ψ`. -/

theorem pureDensity_trace (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    (pureDensity psi).trace = 1 := by
  have : ∀ k : n, psi k * (starRingEnd ℂ) (psi k) = ((‖psi k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq (psi k)
  simp only [Matrix.trace, Matrix.diag_apply, pureDensity_apply, this]
  rw [← Complex.ofReal_sum, hpsi, Complex.ofReal_one]

/-- Every eigenvalue of a Hermitian idempotent matrix is `0` or `1`. -/
