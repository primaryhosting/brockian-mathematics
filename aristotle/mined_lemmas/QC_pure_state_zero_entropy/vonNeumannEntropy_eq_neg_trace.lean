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

theorem vonNeumannEntropy_eq_neg_trace {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = -(ρ * matrixLog hρ).trace.re := by
  set U : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := by
    simp [hU, Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2]
  have hspec : ρ = U * Matrix.diagonal (fun i => ((hρ.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hρ.spectral_theorem]
    simp [hU, Unitary.conjStarAlgAut_apply, Function.comp_def]
  have hprod : ρ * matrixLog hρ =
      U * Matrix.diagonal
        (fun i => ((hρ.eigenvalues i : ℝ) : ℂ) * ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ)) *
      star U := by
    have h := congrArg (fun M => M * matrixLog hρ) hspec
    simp only at h
    rw [h, matrixLog, ← hU, ← Matrix.diagonal_mul_diagonal]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
  have htrace : (ρ * matrixLog hρ).trace
      = ∑ i, ((hρ.eigenvalues i : ℝ) : ℂ) * ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ) := by
    rw [hprod, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
  have hcast : (∑ i, ((hρ.eigenvalues i : ℝ) : ℂ) * ((Real.log (hρ.eigenvalues i) : ℝ) : ℂ))
      = ((∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [htrace, hcast, Complex.ofReal_re, vonNeumannEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.negMulLog]; ring

/-- Every eigenvalue of an idempotent Hermitian matrix is `0` or `1`. -/
