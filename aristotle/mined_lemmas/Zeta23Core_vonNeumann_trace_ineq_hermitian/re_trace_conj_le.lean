import Mathlib
/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of `W`. If `W` is unitary this is a doubly
stochastic matrix. -/

lemma re_trace_conj_le {a b : n → ℝ} (hab : Monovary a b) {U V : Matrix n n 𝕜}
    (hU : U * star U = 1) (hU' : star U * U = 1)
    (hV : V * star V = 1) (hV' : star V * V = 1) :
    RCLike.re (Matrix.trace (U * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U *
        (V * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V))) ≤ ∑ i, a i * b i := by
  set W : Matrix n n 𝕜 := star U * V with hW
  have hstarW : star W = star V * U := by rw [hW, Matrix.star_mul, star_star]
  have hWW : W * star W = 1 := by
    rw [hW, hstarW]
    calc star U * V * (star V * U) = star U * (V * star V) * U := by simp only [mul_assoc]
      _ = 1 := by rw [hV, mul_one, hU']
  have hWW' : star W * W = 1 := by
    rw [hW, hstarW]
    calc star V * U * (star U * V) = star V * (U * star U) * V := by simp only [mul_assoc]
      _ = 1 := by rw [hU, mul_one, hV']
  have htr : Matrix.trace (U * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U *
      (V * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V))
      = Matrix.trace (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * W *
        diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star W) := by
    have e1 : U * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U *
        (V * diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V)
        = U * (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ a) * star U * V *
          diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ b) * star V) := by
      simp only [mul_assoc]
    rw [e1, Matrix.trace_mul_comm, hstarW, hW]
    congr 1
    simp only [mul_assoc]
  rw [htr, re_trace_diag_mul]
  exact sum_mul_mul_le_of_mem_doublyStochastic hab
    (weightMatrix_mem_doublyStochastic hWW hWW')

