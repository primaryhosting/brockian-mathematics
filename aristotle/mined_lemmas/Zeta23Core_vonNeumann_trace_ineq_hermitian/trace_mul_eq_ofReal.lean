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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

section Rearrangement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Value of the bilinear form `M ↦ ∑ j, ∑ k, M j k * (a j * b k)` at a permutation matrix. -/

lemma trace_mul_eq_ofReal (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace
      = ((∑ j, ∑ k, eigWeight hA hB j k * (hA.eigenvalues j * hB.eigenvalues k) : ℝ) : 𝕜) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  set V : Matrix n n 𝕜 := (hB.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set a : n → ℝ := hA.eigenvalues with ha
  set b : n → ℝ := hB.eigenvalues with hb
  set f : n → n → n → n → 𝕜 := fun i j k l =>
    ((a k : 𝕜) * (U i k * (starRingEnd 𝕜) (U j k))) *
      ((b l : 𝕜) * (V j l * (starRingEnd 𝕜) (V i l))) with hf
  have hreorder : ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ p : n × n, ∑ q : n × n, f p.1 p.2 q.1 q.2 by
         simp [Fintype.sum_prod_type],
       show (∑ k, ∑ l, ∑ i, ∑ j, f i j k l) = ∑ q : n × n, ∑ p : n × n, f p.1 p.2 q.1 q.2 by
         simp [Fintype.sum_prod_type]]
    exact Finset.sum_comm
  have hlhs : (A * B).trace = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
    have h1 : (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hermitian_entry hA i j, hermitian_entry hB j i, Finset.sum_mul_sum]
  have hrhs : ((∑ j, ∑ k, eigWeight hA hB j k * (a j * b k) : ℝ) : 𝕜)
      = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    simp only [RCLike.ofReal_sum, RCLike.ofReal_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hW : ((eigWeight hA hB k l : ℝ) : 𝕜)
        = (starRingEnd 𝕜) (eigTransition hA hB k l) * (eigTransition hA hB k l) := by
      rw [RCLike.conj_mul]
      simp [eigWeight]
    have hWkl : eigTransition hA hB k l = ∑ j, (starRingEnd 𝕜) (U j k) * V j l := by
      simp [eigTransition, Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, hU, hV]
    have hWc : (starRingEnd 𝕜) (eigTransition hA hB k l)
        = ∑ i, U i k * (starRingEnd 𝕜) (V i l) := by
      rw [hWkl, map_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
    rw [hW, hWc, hWkl, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf]
    ring
  rw [hlhs, hreorder, ← hrhs]

/-- `Re tr (A * B) = ∑_{jk} |W_{jk}|² a_j b_k`. -/
