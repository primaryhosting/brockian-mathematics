/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The proof follows the classical route: writing `A = U Dα U*`, `B = V Dβ V*` via the spectral
theorem, one gets `tr (A B) = ∑ j k, α j * β k * |W j k|²` for the unitary `W = U* V`.
The matrix of squared moduli of a unitary matrix is doubly stochastic, so by Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) the right-hand side is a convex combination of the
quantities `∑ j, α j * β (σ j)`, each of which is bounded by `∑ i, a i * b i` by the rearrangement
inequality (`Monovary.sum_mul_comp_perm_le_sum_mul`).
-/

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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a matrix. -/

lemma weightMatrix_mem_doublyStochastic {W : Matrix n n 𝕜} (h1 : W * star W = 1)
    (h2 : star W * W = 1) : weightMatrix W ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun j k => by simp only [weightMatrix]; positivity, fun j => ?_, fun k => ?_⟩
  · have e : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = (W * star W) j j := by
      rw [Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.star_apply, show (star (W j k)) = starRingEnd 𝕜 (W j k) from rfl,
        RCLike.mul_conj]
    rw [h1, Matrix.one_apply_eq] at e
    simp only [weightMatrix]
    exact_mod_cast e
  · have e : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = (star W * W) k k := by
      rw [Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.star_apply, show (star (W j k)) = starRingEnd 𝕜 (W j k) from rfl,
        RCLike.conj_mul]
    rw [h2, Matrix.one_apply_eq] at e
    simp only [weightMatrix]
    exact_mod_cast e

/-- Trace of `diagonal a * W * diagonal b * star W` as a weighted double sum. -/
