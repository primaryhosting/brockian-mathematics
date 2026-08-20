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

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Functional calculus for a Hermitian matrix: `hermFun hρ f` is the matrix obtained by
applying the real function `f` to the eigenvalues of `ρ`, in an eigenbasis of `ρ`. -/

lemma pureState_idem (ψ : n → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    pureState ψ * pureState ψ = pureState ψ := by
  ext i j
  simp only [pureState, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def]
  have : ∑ k, ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
      = (ψ i * (starRingEnd ℂ) (ψ j)) * ∑ k, ((‖ψ k‖ : ℝ) : ℂ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (starRingEnd ℂ) (ψ k) * ψ k = ((‖ψ k‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.conj_mul']
    calc ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
        = (ψ i * (starRingEnd ℂ) (ψ j)) * ((starRingEnd ℂ) (ψ k) * ψ k) := by ring
      _ = (ψ i * (starRingEnd ℂ) (ψ j)) * ((‖ψ k‖ : ℝ) : ℂ) ^ 2 := by rw [hk]
  rw [this]
  have : ∑ k, ((‖ψ k‖ : ℝ) : ℂ) ^ 2 = 1 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hψ
    push_cast at this
    simpa using this
  rw [this, mul_one]

/-- **The von Neumann entropy of a pure state is zero.** -/
