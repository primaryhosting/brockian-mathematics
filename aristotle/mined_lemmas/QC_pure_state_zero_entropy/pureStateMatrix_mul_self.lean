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

theorem pureStateMatrix_mul_self (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) :
    pureStateMatrix psi * pureStateMatrix psi = pureStateMatrix psi := by
  have hsum : ∑ k, (starRingEnd ℂ) (psi k) * psi k = 1 := by
    have : ∀ k, (starRingEnd ℂ) (psi k) * psi k = ((‖psi k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq (psi k)
    simp only [this, ← Complex.ofReal_sum, hpsi, Complex.ofReal_one]
  ext i j
  simp only [pureStateMatrix, Matrix.mul_apply, Matrix.of_apply]
  calc ∑ k, psi i * (starRingEnd ℂ) (psi k) * (psi k * (starRingEnd ℂ) (psi j))
      = (∑ k, (starRingEnd ℂ) (psi k) * psi k) * (psi i * (starRingEnd ℂ) (psi j)) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = psi i * (starRingEnd ℂ) (psi j) := by rw [hsum, one_mul]

omit [DecidableEq n] in
/-- Sanity check: a pure-state density matrix built from a unit vector has trace `1`,
so it really is a density matrix. -/
