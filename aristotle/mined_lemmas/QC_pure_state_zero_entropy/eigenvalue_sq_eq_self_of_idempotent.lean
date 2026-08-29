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

theorem eigenvalue_sq_eq_self_of_idempotent {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) (j : n) : (hρ.eigenvalues j) ^ 2 = hρ.eigenvalues j := by
  set v := (hρ.eigenvectorBasis j).ofLp with hv
  have h1 : ρ *ᵥ v = hρ.eigenvalues j • v := hρ.mulVec_eigenvectorBasis j
  have h2 : (ρ * ρ) *ᵥ v = ρ *ᵥ (ρ *ᵥ v) := by rw [Matrix.mulVec_mulVec]
  rw [hidem, h1, Matrix.mulVec_smul, h1] at h2
  have hvne : v ≠ 0 := by
    have := (hρ.eigenvectorBasis).orthonormal.ne_zero j
    simpa [hv] using this
  have hz : ((hρ.eigenvalues j) ^ 2 - hρ.eigenvalues j) • v = 0 := by
    rw [sub_smul, sq, SemigroupAction.mul_smul, ← h2, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h hvne

/-- If `λ² = λ` then `-λ log λ = 0` (since `λ` is `0` or `1`). -/
